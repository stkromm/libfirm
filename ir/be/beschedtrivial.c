/**
 * Trivial node selector.
 * @author Christian Wuerdig
 * @date   29.08.2006
 * @cvs-id $Id$
 */

#include <stdlib.h>

#include "besched_t.h"
#include "belistsched.h"

/**
 * The trivial selector:
 * Just assure that branches are executed last, otherwise select
 * the first node ready.
 */
static ir_node *trivial_select(void *block_env, nodeset *ready_set, nodeset *live_set)
{
	const arch_env_t *arch_env = block_env;
	ir_node          *irn      = NULL;

	/* assure that branches and constants are executed last */
	for (irn = nodeset_first(ready_set); irn; irn = nodeset_next(ready_set)) {
		if (! arch_irn_class_is(arch_env, irn, branch)) {
			nodeset_break(ready_set);
			return irn;
		}
	}

	/* at last: schedule branches */
	irn = nodeset_first(ready_set);
	nodeset_break(ready_set);

	return irn;
}

static void *trivial_init_graph(const list_sched_selector_t *vtab, const arch_env_t *arch_env, ir_graph *irg)
{
	return (void *)arch_env;
}

static void *trivial_init_block(void *graph_env, ir_node *bl)
{
	return graph_env;
}

static const list_sched_selector_t trivial_selector_struct = {
	trivial_init_graph,
	trivial_init_block,
	trivial_select,
	NULL,                /* to_appear_in_schedule */
	NULL,                /* node_ready */
	NULL,                /* node_selected */
	NULL,                /* exectime */
	NULL,                /* latency */
	NULL,                /* finish_block */
	NULL                 /* finish_graph */
};

const list_sched_selector_t *trivial_selector = &trivial_selector_struct;
