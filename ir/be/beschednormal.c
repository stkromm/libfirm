/*
 * This file is part of libFirm.
 * Copyright (C) 2012 University of Karlsruhe.
 */

/**
 * @brief   Schedule using the strong normal form theorem (though it does not
 *          hold)
 * @author  Christoph Mallon
 */
#include "array.h"
#include "belistsched.h"
#include "belive.h"
#include "bemodule.h"
#include "benode.h"
#include "besched.h"
#include "debug.h"
#include "heights.h"
#include "irnode.h"
#include "irgwalk.h"
#include "irprintf.h"
#include "irtools.h"
#include "irouts_t.h"
#include "util.h"
#include <stdlib.h>

DEBUG_ONLY(static firm_dbg_module_t *dbg = NULL;)

static struct obstack obst;
static ir_node       *curr_list;
/**
Callback for backend specific instruction informations
*/
static const instrsched_if_t *instr_info;

typedef struct irn_cost_pair {
	ir_node *irn;
	unsigned cost;
} irn_cost_pair;

typedef struct flag_and_cost {
	bool          no_root;
	unsigned 			maximum_path_latency;
	irn_cost_pair costs[];
} flag_and_cost;

static flag_and_cost *get_irn_flag_and_cost(const ir_node *node)
{
	return (flag_and_cost*)get_irn_link(node);
}

static void set_irn_flag_and_cost(ir_node *node, flag_and_cost *fc)
{
	set_irn_link(node, fc);
}

static ir_node *normal_select(ir_nodeset_t *ready_set)
{
	for (ir_node *irn = curr_list, *last = NULL, *next; irn != NULL;
	     last = irn, irn = next) {
		next = (ir_node*)get_irn_link(irn);
		if (ir_nodeset_contains(ready_set, irn)) {
			DB((dbg, LEVEL_1, "Scheduling %+F\n", irn));
			if (last == NULL)
				curr_list = next;
			else
				set_irn_link(last, next);
			return irn;
		}
	}

	return ir_nodeset_first(ready_set);
}

static int get_instruction_latency(ir_node *node)
{
	if (!instr_info->is_defined(node)) {
		return 0;
	}
	return instr_info->get_latency(node);
}

static unsigned get_maximum_path_latency(ir_node *node)
{
	const flag_and_cost* fc = get_irn_flag_and_cost(node);
	if (!fc) { // For nodes with fc, select the highest mpl of any successor
		if (is_Block(node)) return 0;
		ir_node *block = get_nodes_block(node);

		if (is_Pin(node) || is_Sync(node) || is_Proj(node)) { // Forward virtual nodes
			unsigned max = 0;
			foreach_irn_out(node, index, succ) {
				if (is_Block(succ) || get_nodes_block(succ) != block)
					continue;
				max = MAX(max, get_maximum_path_latency(succ));
			}
			return max;
		} else {
			return 0;
		}
	}
	return fc->maximum_path_latency;
}

/**
Sort by
1. greatest maximum path latency
2. lowest tree register cost
3. greatest successor count
4. lowest index
*/
static int cost_cmp(const void *a, const void *b)
{
	const irn_cost_pair *const a_fc = (const irn_cost_pair*)a;
	const irn_cost_pair *const b_fc = (const irn_cost_pair*)b;

	int ret = 0;
	// Sched by highest maximum path latency
	ret = (int)get_maximum_path_latency(a_fc->irn) - (int)get_maximum_path_latency(b_fc->irn);

	// Tie by lowest register costs
	if (ret == 0) {
		ret = (int)b_fc->cost - (int)a_fc->cost;
	}
	// Tie by highest #succ
	if (ret == 0) {
		ret = (int)get_irn_n_outs(a_fc->irn) - (int)get_irn_n_outs(b_fc->irn);
	}
	// Tie by index
	if (ret == 0) {
		ret = (int)get_irn_idx(b_fc->irn) - (int)get_irn_idx(a_fc->irn);
	}
	return ret;
}

/**
Returns the number of results this node emits
*/
static unsigned count_result(const ir_node *irn)
{
	const ir_mode *mode = get_irn_mode(irn);
	if (mode == mode_M || mode == mode_X) {
		return 0;
	}
	if (mode == mode_T) {
		return 1;
	}
	arch_register_req_t const *const req = arch_get_irn_register_req(irn);
	return req->ignore ? 0 : 1;
}

static void calculate_total_latency(ir_node* irn);
static unsigned get_max_latency_succ(ir_node* irn)
{
	if (is_End(irn)) return 0;
	unsigned max = 0;
	foreach_irn_out(irn, index, succ) {
		ir_node *block = get_nodes_block(irn);
		if (get_nodes_block(succ) != block || is_End(succ) || is_Bad(succ) || succ == irn)
			continue;
		if (is_Pin(succ) || is_Sync(succ) || is_Proj(succ)) {
			max = MAX(max, get_max_latency_succ(succ));
		} else {
			flag_and_cost *fc_succ = get_irn_flag_and_cost(succ);
			calculate_total_latency(succ);
			max = MAX(max, fc_succ->maximum_path_latency);
		}
	}
	return max;
}

/**
* Expects that flag and cost structure are created
*/
static void calculate_total_latency(ir_node* irn)
{
	flag_and_cost *fc    = get_irn_flag_and_cost(irn);
	if (fc && fc->maximum_path_latency != 1337) return;

	if (be_is_Keep(irn) || is_End(irn) || is_Bad(irn))
	{
		if (fc) fc->maximum_path_latency = 0;
		return;
	}
	if (is_Pin(irn) || is_Sync(irn) || is_Proj(irn)) { // Proxy latency calculation to projection consumers
		foreach_irn_out(irn, index, succ) {
			if (succ == irn) continue;
			calculate_total_latency(succ);
		}
		return;
	}

	if (!fc->no_root) { // Recursion end -> just the instruction latency
		DB((dbg, LEVEL_1, "%+F is root and gets just instr latency\n", irn));
		fc->maximum_path_latency = get_instruction_latency(irn);
	} else { // Irn has dependent successors. It's latency is it#s own instruction latency + MAX of successors
		// set the maximum path latency of this node for now to 0 to break cycles in the graph
		fc->maximum_path_latency = 0;
		unsigned max_successor_latency = get_max_latency_succ(irn);
		DB((dbg, LEVEL_1, "%+F uses own latency %d and max succ %d\n", irn, get_instruction_latency(irn), max_successor_latency));
		fc->maximum_path_latency = get_instruction_latency(irn) + max_successor_latency;
	}
	DB((dbg, LEVEL_1, "%+F end calculate total latency %d\n", irn, fc->maximum_path_latency));
}

static unsigned normal_tree_cost(ir_node *irn)
{
	/* TODO: high cost for store trees */
	if (be_is_Keep(irn)) {
		return 0;
	}
	if (is_Proj(irn))
		return normal_tree_cost(get_Proj_pred(irn));

	int            arity = get_irn_arity(irn);
	flag_and_cost *fc    = get_irn_flag_and_cost(irn);
	if (fc == NULL) {
		ir_node *block = get_nodes_block(irn);

		fc = OALLOCF(&obst, flag_and_cost, costs, arity);
		fc->no_root = false;
		fc->maximum_path_latency = 1337;
		irn_cost_pair *costs = fc->costs;

		foreach_irn_in(irn, i, pred) {
			unsigned cost;
				if (is_Phi(irn) || get_irn_mode(pred) == mode_M) {
					cost = 0;
				} else if (get_nodes_block(pred) != block) {
					cost = 1;
				} else {
					cost = normal_tree_cost(pred);
					if (!arch_irn_is_ignore(pred)) {
						ir_node       *real_pred = is_Proj(pred)
						                         ? get_Proj_pred(pred) : pred;
						flag_and_cost *pred_fc = get_irn_flag_and_cost(real_pred);
						pred_fc->no_root = true;
						DB((dbg, LEVEL_1, "%+F says that %+F is no root\n", irn,
						    real_pred));
					}
				}

				costs[i].irn  = pred;
				costs[i].cost = cost;
		}

		// Calculate maximum_path_latency as sum of irn latency and max of all successors
		QSORT(costs, arity, cost_cmp);
		set_irn_flag_and_cost(irn, fc);
	}

	// At this point, all predeccesors of irn have valid costs calculated
	unsigned n_op_res = 0;
	unsigned reg_cost;
	ir_node *last     = 0;

	// For each input node
	for (int i = 0; i < arity; ++i) {
		ir_node *op = fc->costs[i].irn;
		if (op == last)
			continue;
		ir_mode *mode = get_irn_mode(op);
		if (mode == mode_M || arch_irn_is_ignore(op))
			continue;
		reg_cost = MAX(fc->costs[i].cost + n_op_res, reg_cost);
		last = op;
		++n_op_res;
	}
	unsigned n_res = count_result(irn);
	return MAX(n_res, reg_cost);
}

static void maximum_path_latency_walker(ir_node *irn, void *data)
{
	(void)data;
	DB((dbg, LEVEL_1, "maximum path latency walking node %+F\n", irn));
	if (!is_Block(irn) && !arch_is_irn_not_scheduled(irn)) {
		calculate_total_latency(irn);
	}
}

static void normal_cost_walker(ir_node *irn, void *data)
{
	(void)data;
	DB((dbg, LEVEL_1, "cost walking node %+F\n", irn));
	if (is_Block(irn)) {
		ir_node **const roots = NEW_ARR_F(ir_node*, 0);
		set_irn_link(irn, roots);
		return;
	}
	if (arch_is_irn_not_scheduled(irn))
		return;
	normal_tree_cost(irn);
}

static void collect_roots(ir_node *irn, void *env)
{
	(void)env;
	if (arch_is_irn_not_scheduled(irn))
		return;

	bool is_root = be_is_Keep(irn) || !get_irn_flag_and_cost(irn)->no_root;
	DB((dbg, LEVEL_1, "%+F is %sroot\n", irn, is_root ? "" : "no "));
	if (is_root) {
		ir_node  *block = get_nodes_block(irn);
		ir_node **roots = (ir_node**)get_irn_link(block);
		ARR_APP1(ir_node*, roots, irn);
		set_irn_link(block, roots);
	}
}

static ir_node **sched_node(ir_node **sched, ir_node *irn)
{
	if (irn_visited_else_mark(irn))
		return sched;

	if (!is_Phi(irn) && !be_is_Keep(irn)) {
		ir_node       *block = get_nodes_block(irn);
		flag_and_cost *fc    = get_irn_flag_and_cost(irn);
		irn_cost_pair *irns  = fc->costs;
		QSORT(irns, get_irn_arity(irn), cost_cmp);

		for (int i = 0, arity = get_irn_arity(irn); i < arity; ++i) {
			ir_node *pred = irns[i].irn;
			if (get_nodes_block(pred) != block)
				continue;
			if (get_irn_mode(pred) == mode_M)
				continue;
			if (is_Proj(pred))
				pred = get_Proj_pred(pred);
			sched = sched_node(sched, pred);
		}
	}

	ARR_APP1(ir_node*, sched, irn);
	return sched;
}

static int root_cmp(const void *a, const void *b)
{
	const irn_cost_pair *const a1 = (const irn_cost_pair*)a;
	const irn_cost_pair *const b1 = (const irn_cost_pair*)b;
	int ret;
	if (is_cfop(a1->irn) && !is_cfop(b1->irn)) {
		ret = 1;
	} else if (is_cfop(b1->irn) && !is_cfop(a1->irn)) {
		ret = -1;
	} else {
		ret = cost_cmp(a1, b1);
	}
	DB((dbg, LEVEL_1, "root %+F %s %+F\n", a1->irn,
	    ret < 0 ? "<" : ret > 0 ? ">" : "=", b1->irn));
	return ret;
}

static void normal_sched_block(ir_node *block, void *env)
{
	ir_node     **roots   = (ir_node**)get_irn_link(block);
	ir_heights_t *heights = (ir_heights_t*)env;

	DB((dbg, LEVEL_1, "sched walking block %+F\n", block));

	int const root_count = ARR_LEN(roots);
	if (root_count == 0) {
		DB((dbg, LEVEL_1, "has no roots\n"));
		return;
	}

	irn_cost_pair *root_costs = ALLOCAN(irn_cost_pair, root_count);
	for (int i = 0; i < root_count; ++i) {
		root_costs[i].irn  = roots[i];
		root_costs[i].cost = get_irn_height(heights, roots[i]);
		DB((dbg, LEVEL_1, "height of %+F is %u\n", roots[i],
		    root_costs[i].cost));
	}
	QSORT(root_costs, root_count, root_cmp);
#ifdef DEBUG_libfirm
	DB((dbg, LEVEL_1, "Root Scheduling of %+F:\n", block));
	for (int i = 0, n = root_count; i < n; ++i) {
		DB((dbg, LEVEL_1, "  %+F\n", root_costs[i].irn));
	}
	DB((dbg, LEVEL_1, "\n"));
#endif

	ir_node **sched = NEW_ARR_F(ir_node*, 0);
	for (int i = 0; i < root_count; ++i) {
		ir_node *irn = root_costs[i].irn;
		assert(!arch_is_irn_not_scheduled(irn));
		sched = sched_node(sched, irn);
	}
	set_irn_link(block, sched);
	DEL_ARR_F(roots);

#ifdef DEBUG_libfirm
	DB((dbg, LEVEL_1, "Scheduling of %+F:\n", block));
	for (int i = 0, n = ARR_LEN(sched); i < n; ++i) {
		DB((dbg, LEVEL_1, "  %+F\n", sched[i]));
		DB((dbg, LEVEL_1, "maximum path latency is %d\n", (int)get_maximum_path_latency(sched[i])));
	}
	DB((dbg, LEVEL_1, "\n"));
#endif
}

static void real_sched_block(ir_node *block, void *data)
{
	(void)data;
	ir_node **sched = (ir_node**)get_irn_link(block);
	ir_node  *first = NULL;

	/* turn into a list, so we can easily remove nodes. The link field is used
	 * anyway. */
	for (int i = ARR_LEN(sched); i-- > 0; ) {
		ir_node *irn = sched[i];
		set_irn_link(irn, first);
		first = irn;
	}
	/* note: we can free sched here, there should be no attempt to schedule
	 * a block twice */
	DEL_ARR_F(sched);
	set_irn_link(block, sched);
	curr_list = first;

	ir_nodeset_t *cands = be_list_sched_begin_block(block);
	while (ir_nodeset_size(cands) > 0) {
		ir_node *node = normal_select(cands);
		be_list_sched_schedule(node);
	}
	be_list_sched_end_block();
}

static void sched_normal(ir_graph *irg, const instrsched_if_t *instrsched)
{
	/* Initalize resources */
	instr_info = instrsched;
	/* block uses the link field to store the schedule */
	ir_reserve_resources(irg, IR_RESOURCE_IRN_LINK);
	/* used to allocate scheduling decision information structure*/
	obstack_init(&obst);
	irg_walk_graph(irg, firm_clear_link, NULL, NULL);

	/* Prepare scheduling */
	/* Calculates is_root flag and tree costs of each to be scheduled node */
	irg_walk_graph(irg, normal_cost_walker,  NULL, NULL);
	irg_walk_graph(irg, maximum_path_latency_walker,  NULL, NULL);
	/* Creates a list of all roots (= initial ready set)*/
	irg_walk_graph(irg, collect_roots, NULL, NULL);
	{
		ir_heights_t *heights = heights_new(irg);
		ir_reserve_resources(irg, IR_RESOURCE_IRN_VISITED);
		inc_irg_visited(irg);
		// Uses heights as root costs
		irg_block_walk_graph(irg, normal_sched_block, NULL, heights);
		ir_free_resources(irg, IR_RESOURCE_IRN_VISITED);
		heights_free(heights);
	}
	/* Create actual schedule */
	{
		be_list_sched_begin(irg);
		irg_block_walk_graph(irg, real_sched_block, NULL, NULL);
		be_list_sched_finish();
	}
	/* Free resources */
	ir_free_resources(irg, IR_RESOURCE_IRN_LINK);
	obstack_free(&obst, NULL);
	instr_info = NULL;
}

BE_REGISTER_MODULE_CONSTRUCTOR(be_init_sched_normal)
void be_init_sched_normal(void)
{
	be_register_scheduler("normal", sched_normal);
	FIRM_DBG_REGISTER(dbg, "firm.be.sched.normal");
}
