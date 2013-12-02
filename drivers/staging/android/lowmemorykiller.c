/* drivers/misc/lowmemorykiller.c
 *
 * The lowmemorykiller driver lets user-space specify a set of memory thresholds
 * where processes with a range of oom_score_adj values will get killed. Specify
 * the minimum oom_score_adj values in
 * /sys/module/lowmemorykiller/parameters/adj and the number of free pages in
 * /sys/module/lowmemorykiller/parameters/minfree. Both files take a comma
 * separated list of numbers in ascending order.
 *
 * For example, write "0,8" to /sys/module/lowmemorykiller/parameters/adj and
 * "1024,4096" to /sys/module/lowmemorykiller/parameters/minfree to kill
 * processes with a oom_score_adj value of 8 or higher when the free memory
 * drops below 4096 pages and kill processes with a oom_score_adj value of 0 or
 * higher when the free memory drops below 1024 pages.
 *
 * The driver considers memory used for caches to be free, but if a large
 * percentage of the cached memory is locked this can be very inaccurate
 * and processes may not get killed until the normal oom killer is triggered.
 *
 * Copyright (C) 2007-2008 Google, Inc.
 *
 * This software is licensed under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation, and
 * may be copied, distributed, and modified under those terms.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 */

#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/mm.h>
#include <linux/oom.h>
#include <linux/sched.h>
#include <linux/rcupdate.h>
#include <linux/notifier.h>
#include <linux/mutex.h>
#include <linux/delay.h>
#include <linux/swap.h>
#include <linux/fs.h>
#include <linux/kobject.h>
#include <linux/slab.h>

#ifdef CONFIG_HIGHMEM
	#define _ZONE ZONE_HIGHMEM
#else
	#define _ZONE ZONE_NORMAL
#endif


extern void show_meminfo(void);
static uint32_t lowmem_debug_level = 1;
static int lowmem_adj[6] = {
	0,
	1,
	6,
	12,
};
static int lowmem_adj_size = 4;
static int lowmem_minfree[6] = {
	3 * 512,	
	2 * 1024,	
	4 * 1024,	
	16 * 1024,	
};
static int lowmem_minfree_size = 4;

static unsigned long lowmem_deathpending_timeout;
static uint32_t lowmem_sleep_ms = 1;
static uint32_t lowmem_only_kswapd_sleep = 1;

static struct shrink_control lowmem_notif_sc = {GFP_KERNEL, 0};
static size_t lowmem_minfree_notif_trigger;
static struct kobject *lowmem_notify_kobj;

#define lowmem_print(level, x...)			\
	do {						\
		if (lowmem_debug_level >= (level))	\
			printk(x);			\
	} while (0)

static void dump_tasks(void)
{
       struct task_struct *p;
       struct task_struct *task;

       pr_info("[ pid ]   uid  total_vm      rss cpu oom_adj  name\n");
       for_each_process(p) {
               task = find_lock_task_mm(p);
               if (!task) {
                       continue;
               }

               pr_info("[%5d] %5d  %8lu %8lu %3u     %3d  %s\n",
                       task->pid, task_uid(task),
                       task->mm->total_vm, get_mm_rss(task->mm),
                       task_cpu(task), task->signal->oom_adj, task->comm);
               task_unlock(task);
       }
}

static int test_task_flag(struct task_struct *p, int flag)
{
	struct task_struct *t;

	for_each_thread(p,t) {
		task_lock(t);
		if (test_tsk_thread_flag(t, flag)) {
			task_unlock(t);
			return 1;
		}
		task_unlock(t);
	}

	return 0;
}

static DEFINE_MUTEX(scan_mutex);

int can_use_cma_pages(gfp_t gfp_mask)
{
	int can_use = 0;
	int mtype = allocflags_to_migratetype(gfp_mask);
	int i = 0;
	int *mtype_fallbacks = get_migratetype_fallbacks(mtype);

	if (is_migrate_cma(mtype)) {
		can_use = 1;
	} else {
		for (i = 0;; i++) {
			int fallbacktype = mtype_fallbacks[i];

			if (is_migrate_cma(fallbacktype)) {
				can_use = 1;
				break;
			}

			if (fallbacktype == MIGRATE_RESERVE)
				break;
		}
	}
	return can_use;
}

void tune_lmk_zone_param(struct zonelist *zonelist, int classzone_idx,
					int *other_free, int *other_file,
					int use_cma_pages)
{
	struct zone *zone;
	struct zoneref *zoneref;
	int zone_idx;

	for_each_zone_zonelist(zone, zoneref, zonelist, MAX_NR_ZONES) {
		zone_idx = zonelist_zone_idx(zoneref);
		if (zone_idx == ZONE_MOVABLE) {
			if (!use_cma_pages)
				*other_free -=
				    zone_page_state(zone, NR_FREE_CMA_PAGES);
			continue;
		}

		if (zone_idx > classzone_idx) {
			if (other_free != NULL)
				*other_free -= zone_page_state(zone,
							       NR_FREE_PAGES);
			if (other_file != NULL)
				*other_file -= zone_page_state(zone,
							       NR_FILE_PAGES)
					      - zone_page_state(zone, NR_SHMEM);
		} else if (zone_idx < classzone_idx) {
			if (zone_watermark_ok(zone, 0, 0, classzone_idx, 0)) {
				if (!use_cma_pages) {
					*other_free -= min(
					  zone->lowmem_reserve[classzone_idx] +
					  zone_page_state(
					    zone, NR_FREE_CMA_PAGES),
					  zone_page_state(
					    zone, NR_FREE_PAGES));
				} else {
					*other_free -=
					  zone->lowmem_reserve[classzone_idx];
				}
			} else {
				*other_free -=
					   zone_page_state(zone, NR_FREE_PAGES);
			}
		}
	}
}

void tune_lmk_param(int *other_free, int *other_file, struct shrink_control *sc)
{
	gfp_t gfp_mask;
	struct zone *preferred_zone;
	struct zonelist *zonelist;
	enum zone_type high_zoneidx, classzone_idx;
	unsigned long balance_gap;
	int use_cma_pages;

	gfp_mask = sc->gfp_mask;
	zonelist = node_zonelist(0, gfp_mask);
	high_zoneidx = gfp_zone(gfp_mask);
	first_zones_zonelist(zonelist, high_zoneidx, NULL, &preferred_zone);
	classzone_idx = zone_idx(preferred_zone);
	use_cma_pages = can_use_cma_pages(gfp_mask);

	balance_gap = min(low_wmark_pages(preferred_zone),
			  (preferred_zone->present_pages +
			   KSWAPD_ZONE_BALANCE_GAP_RATIO-1) /
			   KSWAPD_ZONE_BALANCE_GAP_RATIO);

	if (likely(current_is_kswapd() && zone_watermark_ok(preferred_zone, 0,
			  high_wmark_pages(preferred_zone) + SWAP_CLUSTER_MAX +
			  balance_gap, 0, 0))) {
		if (lmk_fast_run)
			tune_lmk_zone_param(zonelist, classzone_idx, other_free,
				       other_file, use_cma_pages);
		else
			tune_lmk_zone_param(zonelist, classzone_idx, other_free,
				       NULL, use_cma_pages);

		if (zone_watermark_ok(preferred_zone, 0, 0, _ZONE, 0)) {
			if (!use_cma_pages) {
				*other_free -= min(
				  preferred_zone->lowmem_reserve[_ZONE]
				  + zone_page_state(
				    preferred_zone, NR_FREE_CMA_PAGES),
				  zone_page_state(
				    preferred_zone, NR_FREE_PAGES));
			} else {
				*other_free -=
				  preferred_zone->lowmem_reserve[_ZONE];
			}
		} else {
			*other_free -= zone_page_state(preferred_zone,
						      NR_FREE_PAGES);
		}

		lowmem_print(4, "lowmem_shrink of kswapd tunning for highmem "
			     "ofree %d, %d\n", *other_free, *other_file);
	} else {
		tune_lmk_zone_param(zonelist, classzone_idx, other_free,
			       other_file, use_cma_pages);

		if (!use_cma_pages) {
			*other_free -=
			  zone_page_state(preferred_zone, NR_FREE_CMA_PAGES);
		}

		lowmem_print(4, "lowmem_shrink tunning for others ofree %d, "
			     "%d\n", *other_free, *other_file);
	}
}

static void lowmem_notify_killzone_approach(void);

static int get_free_ram(int *other_free, int *other_file,
		             struct shrink_control *sc)
{
	*other_free = global_page_state(NR_FREE_PAGES);

	if (global_page_state(NR_SHMEM) + total_swapcache_pages <
		global_page_state(NR_FILE_PAGES))
		*other_file = global_page_state(NR_FILE_PAGES) -
						global_page_state(NR_SHMEM) -
						total_swapcache_pages;
	else
		*other_file = 0;

	tune_lmk_param(other_free, other_file, sc);

	if (*other_free < lowmem_minfree_notif_trigger &&
			*other_file < lowmem_minfree_notif_trigger)
		return 1;
	else
		return 0;
}

static int lowmem_shrink(struct shrinker *s, struct shrink_control *sc)
{
	struct task_struct *tsk;
	struct task_struct *selected = NULL;
	int rem = 0;
	int tasksize;
	int i;
	int min_score_adj = OOM_SCORE_ADJ_MAX + 1;
	int selected_tasksize = 0;
	int selected_oom_score_adj;
	int selected_oom_adj = 0;
	int array_size = ARRAY_SIZE(lowmem_adj);
	int other_free;
	int other_file;
	int reserved_free = 0;
	int cma_free = 0;
	unsigned long nr_to_scan = sc->nr_to_scan;
	struct zone *zone;
	int use_cma = can_use_cma_pages(sc->gfp_mask);

	if (nr_to_scan > 0) {
		if (!mutex_trylock(&scan_mutex)) {
			if (!(lowmem_only_kswapd_sleep && !current_is_kswapd())) {
				msleep_interruptible(lowmem_sleep_ms);
			}
			return 0;
		}
	}

	for_each_zone(zone)
	{
		if (is_normal(zone))
			reserved_free = zone->watermark[WMARK_MIN] + zone->lowmem_reserve[_ZONE];

		cma_free += zone_page_state(zone, NR_FREE_CMA_PAGES);
	}

	lowmem_notif_sc.gfp_mask = sc->gfp_mask;

	if (get_free_ram(&other_free, &other_file, sc))
		lowmem_notify_killzone_approach();

	if (lowmem_adj_size < array_size)
		array_size = lowmem_adj_size;
	if (lowmem_minfree_size < array_size)
		array_size = lowmem_minfree_size;
	for (i = 0; i < array_size; i++) {
		if ((other_free - reserved_free - (use_cma ? 0 : cma_free)) < lowmem_minfree[i] &&
		    other_file < lowmem_minfree[i]) {
			min_score_adj = lowmem_adj[i];
			break;
		}
	}
	if (nr_to_scan > 0)
		lowmem_print(3, "lowmem_shrink %lu, %x, ofree %d %d, ma %d, rfree %d\n",
				nr_to_scan, sc->gfp_mask, other_free,
				other_file, min_score_adj, reserved_free);
	rem = global_page_state(NR_ACTIVE_ANON) +
		global_page_state(NR_ACTIVE_FILE) +
		global_page_state(NR_INACTIVE_ANON) +
		global_page_state(NR_INACTIVE_FILE);
	if (nr_to_scan <= 0 || min_score_adj == OOM_SCORE_ADJ_MAX + 1) {
		lowmem_print(5, "lowmem_shrink %lu, %x, return %d\n",
			     nr_to_scan, sc->gfp_mask, rem);

		if (nr_to_scan > 0)
			mutex_unlock(&scan_mutex);

		return rem;
	}
	selected_oom_score_adj = min_score_adj;

	rcu_read_lock();
	for_each_process(tsk) {
		struct task_struct *p;
		int oom_score_adj;

		if (tsk->flags & PF_KTHREAD)
			continue;

		
		if (test_task_flag(tsk, TIF_MM_RELEASED))
			continue;

		if (time_before_eq(jiffies, lowmem_deathpending_timeout)) {
			if (test_task_flag(tsk, TIF_MEMDIE)) {
				lowmem_print(2, "skipping , waiting for process %d (%s) dead\n",
				tsk->pid, tsk->comm);
				rcu_read_unlock();
				
				if (!(lowmem_only_kswapd_sleep && !current_is_kswapd())) {
					msleep_interruptible(lowmem_sleep_ms);
				}
				mutex_unlock(&scan_mutex);
				return 0;
			}
		}

		p = find_lock_task_mm(tsk);
		if (!p)
			continue;

		oom_score_adj = p->signal->oom_score_adj;
		if (oom_score_adj < min_score_adj) {
			task_unlock(p);
			continue;
		}
		tasksize = get_mm_rss(p->mm);
		task_unlock(p);
		if (tasksize <= 0)
			continue;
		if (selected) {
			if (oom_score_adj < selected_oom_score_adj)
				continue;
			if (oom_score_adj == selected_oom_score_adj &&
			    tasksize <= selected_tasksize)
				continue;
		}
		selected = p;
		selected_tasksize = tasksize;
		selected_oom_score_adj = oom_score_adj;
		selected_oom_adj = p->signal->oom_adj;
		lowmem_print(2, "select %d (%s), oom_adj %d score_adj %d, size %d, to kill\n",
			     p->pid, p->comm, selected_oom_adj, oom_score_adj, tasksize);
	}
	if (selected) {
		bool should_dump_meminfo = false;

		lowmem_print(1, "[%s] send sigkill to %d (%s), oom_adj %d, score_adj %d,"
			" min_score_adj %d, size %dK, free %dK, file %dK, "
			" reserved_free %dK, cma_free %dK, use_cma %d\n",
			     current->comm, selected->pid, selected->comm,
			     selected_oom_adj, selected_oom_score_adj,
			     min_score_adj, selected_tasksize << 2,
			     other_free << 2, other_file << 2, reserved_free << 2, cma_free << 2, use_cma);

		lowmem_deathpending_timeout = jiffies + HZ;
#ifdef CONFIG_ANDROID_LOW_MEMORY_KILLER_AUTODETECT_OOM_ADJ_VALUES
#define DUMP_INFO_OOM_SCORE_ADJ_THRESHOLD	((7 * OOM_SCORE_ADJ_MAX) / -OOM_DISABLE)
		if (selected_oom_score_adj < DUMP_INFO_OOM_SCORE_ADJ_THRESHOLD)
#else
		if (selected->signal->oom_adj < 7)
#endif
			should_dump_meminfo = true;
		send_sig(SIGKILL, selected, 0);
		set_tsk_thread_flag(selected, TIF_MEMDIE);
		rem -= selected_tasksize;
		rcu_read_unlock();

		if (should_dump_meminfo) {
			show_meminfo();
			dump_tasks();
		}

		
		if (!(lowmem_only_kswapd_sleep && !current_is_kswapd()))
			msleep_interruptible(lowmem_sleep_ms);
	} else
		rcu_read_unlock();

	lowmem_print(4, "lowmem_shrink %lu, %x, return %d\n",
		     nr_to_scan, sc->gfp_mask, rem);
	mutex_unlock(&scan_mutex);
	return rem;
}

static struct shrinker lowmem_shrinker = {
	.shrink = lowmem_shrink,
	.seeks = DEFAULT_SEEKS * 16
};

static void lowmem_notify_killzone_approach(void)
{
	lowmem_print(3, "notification trigger activated\n");
	sysfs_notify(lowmem_notify_kobj, NULL,
			"notify_trigger_active");
}

static ssize_t lowmem_notify_trigger_active_show(struct kobject *k,
				struct kobj_attribute *attr, char *buf)
{
	int other_free, other_file;
	if (get_free_ram(&other_free, &other_file, &lowmem_notif_sc))
		return snprintf(buf, 3, "1\n");
	else
		return snprintf(buf, 3, "0\n");
}

static struct kobj_attribute lowmem_notify_trigger_active_attr =
	__ATTR(notify_trigger_active, S_IRUGO,
			lowmem_notify_trigger_active_show, NULL);

static struct attribute *lowmem_notify_default_attrs[] = {
	&lowmem_notify_trigger_active_attr.attr, NULL,
};

static ssize_t lowmem_show(struct kobject *k, struct attribute *attr, char *buf)
{
	struct kobj_attribute *kobj_attr;
	kobj_attr = container_of(attr, struct kobj_attribute, attr);
	return kobj_attr->show(k, kobj_attr, buf);
}

static const struct sysfs_ops lowmem_notify_ops = {
	.show = lowmem_show,
};

static void lowmem_notify_kobj_release(struct kobject *kobj)
{
	/* Nothing to be done here */
}

static struct kobj_type lowmem_notify_kobj_type = {
	.release = lowmem_notify_kobj_release,
	.sysfs_ops = &lowmem_notify_ops,
	.default_attrs = lowmem_notify_default_attrs,
};

static int __init lowmem_init(void)
{
	int rc;

	lowmem_notify_kobj = kzalloc(sizeof(*lowmem_notify_kobj), GFP_KERNEL);
	if(!lowmem_notify_kobj) {
		return -ENOMEM;
	}

	rc = kobject_init_and_add(lowmem_notify_kobj, &lowmem_notify_kobj_type,
			mm_kobj, "lowmemkiller");
	if(rc) {
		kfree(lowmem_notify_kobj);
		return rc;
	}

	register_shrinker(&lowmem_shrinker);

	return 0;
}

static void __exit lowmem_exit(void)
{
	kobject_put(lowmem_notify_kobj);
	kfree(lowmem_notify_kobj);
	unregister_shrinker(&lowmem_shrinker);
}

#ifdef CONFIG_ANDROID_LOW_MEMORY_KILLER_AUTODETECT_OOM_ADJ_VALUES
static int lowmem_oom_adj_to_oom_score_adj(int oom_adj)
{
	if (oom_adj == OOM_ADJUST_MAX)
		return OOM_SCORE_ADJ_MAX;
	else
		return (oom_adj * OOM_SCORE_ADJ_MAX) / -OOM_DISABLE;
}

static void lowmem_autodetect_oom_adj_values(void)
{
	int i;
	int oom_adj;
	int oom_score_adj;
	int array_size = ARRAY_SIZE(lowmem_adj);

	if (lowmem_adj_size < array_size)
		array_size = lowmem_adj_size;

	if (array_size <= 0)
		return;

	oom_adj = lowmem_adj[array_size - 1];
	if (oom_adj > OOM_ADJUST_MAX)
		return;

	oom_score_adj = lowmem_oom_adj_to_oom_score_adj(oom_adj);
	if (oom_score_adj <= OOM_ADJUST_MAX)
		return;

	lowmem_print(1, "lowmem_shrink: convert oom_adj to oom_score_adj:\n");
	for (i = 0; i < array_size; i++) {
		oom_adj = lowmem_adj[i];
		oom_score_adj = lowmem_oom_adj_to_oom_score_adj(oom_adj);
		lowmem_adj[i] = oom_score_adj;
		lowmem_print(1, "oom_adj %d => oom_score_adj %d\n",
			     oom_adj, oom_score_adj);
	}
}

static int lowmem_adj_array_set(const char *val, const struct kernel_param *kp)
{
	int ret;

	ret = param_array_ops.set(val, kp);

	
	lowmem_autodetect_oom_adj_values();

	return ret;
}

static int lowmem_adj_array_get(char *buffer, const struct kernel_param *kp)
{
	return param_array_ops.get(buffer, kp);
}

static void lowmem_adj_array_free(void *arg)
{
	param_array_ops.free(arg);
}

static struct kernel_param_ops lowmem_adj_array_ops = {
	.set = lowmem_adj_array_set,
	.get = lowmem_adj_array_get,
	.free = lowmem_adj_array_free,
};

static const struct kparam_array __param_arr_adj = {
	.max = ARRAY_SIZE(lowmem_adj),
	.num = &lowmem_adj_size,
	.ops = &param_ops_int,
	.elemsize = sizeof(lowmem_adj[0]),
	.elem = lowmem_adj,
};
#endif

module_param_named(cost, lowmem_shrinker.seeks, int, S_IRUGO | S_IWUSR);
#ifdef CONFIG_ANDROID_LOW_MEMORY_KILLER_AUTODETECT_OOM_ADJ_VALUES
__module_param_call(MODULE_PARAM_PREFIX, adj,
		    &lowmem_adj_array_ops,
		    .arr = &__param_arr_adj,
		    S_IRUGO | S_IWUSR, -1);
__MODULE_PARM_TYPE(adj, "array of int");
#else
module_param_array_named(adj, lowmem_adj, int, &lowmem_adj_size,
			 S_IRUGO | S_IWUSR);
#endif
module_param_array_named(minfree, lowmem_minfree, uint, &lowmem_minfree_size,
			 S_IRUGO | S_IWUSR);
module_param_named(debug_level, lowmem_debug_level, uint, S_IRUGO | S_IWUSR);
module_param_named(lmk_fast_run, lmk_fast_run, int, S_IRUGO | S_IWUSR);
module_param_named(notify_trigger, lowmem_minfree_notif_trigger, uint,
			 S_IRUGO | S_IWUSR);

module_init(lowmem_init);
module_exit(lowmem_exit);

MODULE_LICENSE("GPL");

