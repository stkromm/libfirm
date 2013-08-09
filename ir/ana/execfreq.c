/*
 * This file is part of libFirm.
 * Copyright (C) 2012 University of Karlsruhe.
 */

/**
 * @file
 * @brief       Compute an estimate of basic block executions.
 * @author      Adam M. Szalkowski
 * @date        28.05.2006
 *
 * Estimate execution frequencies. We do this by creating a system of linear
 * equations with the following observations:
 *   - Each edge leaving a block (block successors, not block_cfgpreds) has
 *     a probabilty between 0 and 1.0 that it is taken.
 *   - The execution frequencies of a basic block is the sum of all execution
 *     frequencies of its predecessor blocks scaled by the probability factors
 *     of the edges to the predecessors.
 *   - All outgoing probabilities have a sum of 1.0.
 * We then assign equaly distributed probablilities for normal controlflow
 * splits, and higher probabilities for backedges.
 *
 * Special case: In case of endless loops or "noreturn" calls some blocks have
 * no path to the end node, which produces undesired results (0, infinite
 * execution frequencies). We aleviate that by adding artificial edges from kept
 * blocks with a path to end.
 */
#include <stdio.h>
#include <string.h>
#include <limits.h>
#include <math.h>

#include "gaussjordan.h"
#include "gaussseidel.h"

#include "set.h"
#include "hashptr.h"
#include "debug.h"
#include "statev_t.h"
#include "dfs_t.h"
#include "absgraph.h"
#include "error.h"

#include "irprog_t.h"
#include "irgraph_t.h"
#include "irnode_t.h"
#include "irloop.h"
#include "irgwalk.h"
#include "iredges.h"
#include "irouts.h"
#include "util.h"
#include "irhooks.h"
#include "irnodehashmap.h"

#include "execfreq_t.h"

#define EPSILON          1e-5
#define UNDEF(x)         (fabs(x) < EPSILON)
#define SEIDEL_TOLERANCE 1e-7
#define KEEP_FAC         0.1

#define MAX_INT_FREQ 1000000

static hook_entry_t hook;

double get_block_execfreq(const ir_node *block)
{
	return block->attr.block.execfreq;
}

void set_block_execfreq(ir_node *block, double newfreq)
{
	assert(!isinf(newfreq) && newfreq >= 0);
	block->attr.block.execfreq = newfreq;
}

static void exec_freq_node_info(void *ctx, FILE *f, const ir_node *irn)
{
	(void)ctx;
	if (!is_Block(irn))
		return;
	double freq = get_block_execfreq(irn);
	if (freq != 0.0)
		fprintf(f, "execution frequency: %g\n", freq);
}

void init_execfreq(void)
{
	memset(&hook, 0, sizeof(hook));
	hook.hook._hook_node_info = exec_freq_node_info;
	register_hook(hook_node_info, &hook);
}

void exit_execfreq(void)
{
	unregister_hook(hook_node_info, &hook);
}


static int solve_lgs(double *mat, double *x, int size)
{
	/* better convergence. */
	double init = 1.0 / size;
	for (int i = 0; i < size; ++i)
		x[i] = init;

	stat_ev_dbl("execfreq_matrix_size", size);
	stat_ev_tim_push();
	int result = firm_gaussjordansolve(mat, x, size);
	stat_ev_tim_pop("execfreq_seidel_time");

	return result;
}

static bool has_path_to_end(const ir_node *block)
{
	return Block_block_visited(block);
}

static bool is_kept_block(const ir_node *block)
{
	return irn_visited(block);
}

static double get_sum_succ_factors(const ir_node *block, double inv_loop_weight)
{
	const ir_loop *loop  = get_irn_loop(block);
	const int      depth = get_loop_depth(loop);

	double sum = 0.0;
	foreach_block_succ(block, edge) {
		const ir_node *succ       = get_edge_src_irn(edge);
		const ir_loop *succ_loop  = get_irn_loop(succ);
		int            succ_depth = get_loop_depth(succ_loop);

		double fac = 1.0;
		for (int d = succ_depth; d < depth; ++d) {
			fac *= inv_loop_weight;
		}
		sum += fac;
	}

	/* we add an artifical edge from each kept block which has no path to the
	 * end node */
	if (is_kept_block(block) && !has_path_to_end(block))
		sum += KEEP_FAC;

	return sum;
}

/*
 * Determine probability that predecessor pos takes this cf edge.
 */
static double get_cf_probability(const ir_node *bb, int pos,
                                 double inv_loop_weight)
{
	const ir_node *pred = get_Block_cfgpred_block(bb, pos);
	if (is_Bad(pred))
		return 0;

	const ir_loop *loop       = get_irn_loop(bb);
	const int      depth      = get_loop_depth(loop);
	const ir_loop *pred_loop  = get_irn_loop(pred);
	const int      pred_depth = get_loop_depth(pred_loop);

	double cur = 1.0;
	for (int d = depth; d < pred_depth; ++d) {
		cur *= inv_loop_weight;
	}
	double sum = get_sum_succ_factors(pred, inv_loop_weight);

	return cur/sum;
}

static double *freqs;
static double  min_non_zero;
static double  max_freq;

static void collect_freqs(ir_node *node, void *data)
{
	(void) data;
	double freq = get_block_execfreq(node);
	if (freq > max_freq)
		max_freq = freq;
	if (freq > 0.0 && freq < min_non_zero)
		min_non_zero = freq;
	ARR_APP1(double, freqs, freq);
}

void ir_calculate_execfreq_int_factors(ir_execfreq_int_factors *factors,
                                       ir_graph *irg)
{
	/* compute m and b of the transformation used to convert the doubles into
	 * scaled ints */
	freqs = NEW_ARR_F(double, 0);
	min_non_zero = HUGE_VAL;
	max_freq     = 0.0;
	irg_block_walk_graph(irg, collect_freqs, NULL, NULL);

	/*
	 * find the smallest difference of the execution frequencies
	 * we try to ressolve it with 1 integer.
	 */
	size_t n_freqs       = ARR_LEN(freqs);
	double smallest_diff = 1.0;
	for (size_t i = 0; i < n_freqs; ++i) {
		if (freqs[i] <= 0.0)
			continue;

		for (size_t j = i + 1; j < n_freqs; ++j) {
			double diff = fabs(freqs[i] - freqs[j]);

			if (!UNDEF(diff))
				smallest_diff = MIN(diff, smallest_diff);
		}
	}

	double l2 = min_non_zero;
	double h2 = max_freq;
	double l1 = 1.0;
	double h1 = MAX_INT_FREQ;

	/* according to that the slope of the translation function is
	 * 1.0 / smallest_diff */
	factors->m = 1.0 / smallest_diff;

	/* the abscissa is then given by */
	factors->b = l1 - factors->m * l2;

	factors->min_non_zero = min_non_zero;

	/*
	 * if the slope is so high that the largest integer would be larger than
	 * MAX_INT_FREQ set the largest int freq to that upper limit and recompute
	 * the translation function
	 */
	if (factors->m * h2 + factors->b > MAX_INT_FREQ) {
		factors->m = (h1 - l1) / (h2 - l2);
		factors->b = l1 - factors->m * l2;
	}

	DEL_ARR_F(freqs);
}

int get_block_execfreq_int(const ir_execfreq_int_factors *factors,
                           const ir_node *block)
{
	assert(factors->min_non_zero > 0.0);
	assert(factors->m != 0.0);
	double f   = get_block_execfreq(block);
	int    res = (int) (f > factors->min_non_zero ? factors->m * f + factors->b : 1.0);
	return res;
}

static void block_walk_no_keeps(ir_node *block)
{
	if (Block_block_visited(block))
		return;
	mark_Block_block_visited(block);

	for (int n_block_cfgspreds = get_Block_n_cfgpreds(block), i = 0;
	     i < n_block_cfgspreds; ++i) {
	    ir_node *cfgpred_block = get_Block_cfgpred_block(block, i);
	    block_walk_no_keeps(cfgpred_block);
	}
}

/**
 * Computes acc += x * weight, where acc and x are vectors.
 */
static void add_weighted(double *acc, double *x, double weight, int size)
{
	for (int i = 0; i < size; i++) {
		acc[i] += x[i] * weight;
	}
}

/**
 * Computes dot(factors, freqs) where factors and freqs are vectors.
 * If factors[i] == 0, freqs[i] is not read and may be not finite.
 */
static double eval_factors(double *factors, double *freqs, int size)
{
	double acc = 0.0;
	for (int i = 0; i < size; i++) {
		if (factors[i] != 0) {
			assert(isfinite(freqs[i]));
			acc += factors[i] * freqs[i];
		}
	}
	return acc;
}

void ir_estimate_execfreq(ir_graph *irg)
{
	double loop_weight = 10.0;

	assure_irg_properties(irg,
		IR_GRAPH_PROPERTY_CONSISTENT_OUT_EDGES
		| IR_GRAPH_PROPERTY_NO_BADS
		| IR_GRAPH_PROPERTY_CONSISTENT_LOOPINFO
		| IR_GRAPH_PROPERTY_NO_UNREACHABLE_CODE);

	/* compute a DFS.
	 * using a toposort on the CFG (without back edges) will propagate
	 * the values better for the gauss/seidel iteration.
	 * => they can "flow" from start to end. */
	dfs_t *dfs = dfs_new(&absgraph_irg_cfg_succ, irg);

	int     size   = dfs_get_n_nodes(dfs);
	double *in_fac = (double *)malloc(size * size * sizeof(double));
	memset(in_fac, 0, size * size * sizeof(double));

#define ROW(m,r) (m + (size * (r)))
#define ENTRY(m,r,c) (m[size * (r) + (c)])

	ir_node *const start_block = get_irg_start_block(irg);
	ir_node *const end_block   = get_irg_end_block(irg);
	const int      end_idx     = size - dfs_get_post_num(dfs, end_block) - 1;

	ir_reserve_resources(irg, IR_RESOURCE_BLOCK_VISITED
	                     | IR_RESOURCE_IRN_VISITED
			     | IR_RESOURCE_IRN_LINK);
	inc_irg_block_visited(irg);

	/* mark all blocks reachable from end_block as (block)visited
	 * (so we can detect places like endless-loops/noreturn calls which
	 *  do not reach the End block) */
	block_walk_no_keeps(end_block);
	/* mark all kept blocks as (node)visited */
	inc_irg_visited(irg);
	const ir_node *end          = get_irg_end(irg);
	int const      n_keepalives = get_End_n_keepalives(end);
	for (int k = n_keepalives - 1; k >= 0; --k) {
		ir_node *keep = get_End_keepalive(end, k);
		if (is_Block(keep)) {
			mark_irn_visited(keep);
		}
	}

	double const inv_loop_weight = 1.0 / loop_weight;
	/* lgs_to_mat[i] is the index of the block represented by the
	 * i-th row/column in the LGS matrix. */
	int *lgs_to_mat = NEW_ARR_F(int, 0);

	for (int idx = 0; idx < size; idx++) {
		const ir_node *bb = (ir_node*)dfs_get_post_num_node(dfs, size-idx-1);

		if (bb == end_block) {
			/* The end block is handled properly later,
			 * when all the kept blocks are done. */
			continue;
		}

		for (int i = get_Block_n_cfgpreds(bb) - 1; i >= 0; --i) {
			const ir_node *pred           = get_Block_cfgpred_block(bb, i);
			int            pred_idx       = size - dfs_get_post_num(dfs, pred)-1;
			double         cf_probability = get_cf_probability(bb, i, inv_loop_weight);
			bool           pred_visited   = pred_idx < idx;

			if (pred_visited) {
				add_weighted(ROW(in_fac, idx), ROW(in_fac, pred_idx), cf_probability, size);
			} else {
				ARR_APP1(int, lgs_to_mat, pred_idx);
				ENTRY(in_fac, idx, pred_idx) = cf_probability;
			}
		}

		if (bb == start_block) {
			ENTRY(in_fac, idx, end_idx) = 1.0;
		}
	}

	/* Now correct the end block */ {
		const ir_node *bb = end_block;
		int idx = end_idx;

		ARR_APP1(int, lgs_to_mat, idx);

		for (int i = get_Block_n_cfgpreds(bb) - 1; i >= 0; --i) {
			const ir_node *pred           = get_Block_cfgpred_block(bb, i);
			int            pred_idx       = size - dfs_get_post_num(dfs, pred)-1;
			double         cf_probability = get_cf_probability(bb, i, inv_loop_weight);

			add_weighted(ROW(in_fac, idx), ROW(in_fac, pred_idx), cf_probability, size);
		}

		/* add artifical edges from "kept blocks without a path to end"
		 * to end */
		for (int k = n_keepalives - 1; k >= 0; --k) {
			ir_node *keep = get_End_keepalive(end, k);
			if (!is_Block(keep) || has_path_to_end(keep))
				continue;

			double sum      = get_sum_succ_factors(keep, inv_loop_weight);
			double fac      = KEEP_FAC/sum;
			int    keep_idx = size - dfs_get_post_num(dfs, keep)-1;

			add_weighted(ROW(in_fac, idx), ROW(in_fac, keep_idx), fac, size);
		}
	}

	/* mat_to_lgs[i] is the index of node i in the LGS matrix, or
	 * -1 if the node can be solved by simple substitution. */
	int *mat_to_lgs = NEW_ARR_F(int, size);
	for (int x = 0; x < size; x++) {
		mat_to_lgs[x] = -1;
	}
	for (unsigned b = 0; b < ARR_LEN(lgs_to_mat); b++) {
		mat_to_lgs[lgs_to_mat[b]] = b;
	}

#ifdef DEBUG
	/* Check that all values in in_fac are only given in terms of nodes with backedges */
	for (int y = 0; y < size; y++) {
		if (mat_to_lgs[y] != -1) {
			for (int x = 0; x < size; x++) {
				if (ENTRY(in_fac, x, y) != 0) {
					panic("Expect entry at (%d, %d) to be 0.\n", x, y);
				}
			}
		}
	}
#endif

	/* Build the LGS matrix with only the indices in lgs_to_mat. */
	/* Beware! ROW and ENTRY can only be used for in_fac. To avoid
	 * confusion, they are not used here at all. */
	unsigned lgs_size = ARR_LEN(lgs_to_mat);
	double *lgs_matrix = XMALLOCNZ(double, size * size);
	double *lgs_x = XMALLOCNZ(double, size);

	for (unsigned x = 0; x < lgs_size; x++) {
		int bx = lgs_to_mat[x];
		for (unsigned y = 0; y < lgs_size; y++) {
			int by = lgs_to_mat[y];
			lgs_matrix[x * lgs_size + y] = in_fac[bx * size + by];
		}
		lgs_matrix[x * lgs_size + x] -= 1.0; /* RHS of the equation */
	}

	bool valid_freq;
	if (lgs_size == 1) {
		lgs_x[0] = 1.0;
		valid_freq = true;
	} else {
		int  lgs_result = solve_lgs(lgs_matrix, lgs_x, lgs_size);
		valid_freq = !lgs_result; /* solve_lgs returns -1 on error. */
	}


	/* compute the normalization factor.
	 * 1.0 / exec freq of end block.
	 */
	double end_freq = lgs_x[mat_to_lgs[end_idx]];
	double norm     = end_freq != 0.0 ? 1.0 / end_freq : 1.0;

	if (valid_freq) {
		double *freqs = NEW_ARR_F(double, size);

		/* First get the frequency for the nodes which were
		 * explicitly computed. */
		for (int idx = size - 1; idx >= 0; --idx) {
			ir_node *bb = (ir_node *) dfs_get_post_num_node(dfs, size - idx - 1);

			if (mat_to_lgs[idx] != -1) {
				double freq = lgs_x[mat_to_lgs[idx]] * norm;
				/* Check for inf, nan and negative values. */
				if (isinf(freq) || !(freq >= 0)) {
					valid_freq = false;
					break;
				}
				set_block_execfreq(bb, freq);
				freqs[idx] = freq;
			} else {
				freqs[idx] = nan("");
			}
		}

		if (valid_freq) {
			/* Now get the rest of the frequencies using the factors in in_fac */
			for (int idx = size - 1; idx >= 0; --idx) {
				ir_node *bb = (ir_node *) dfs_get_post_num_node(dfs, size - idx - 1);

				if (mat_to_lgs[idx] == -1) {
					double freq = eval_factors(ROW(in_fac, idx), freqs, size);
					/* Check for inf, nan and negative values. */
					if (isinf(freq) || !(freq >= 0)) {
						valid_freq = false;
						break;
					}
					set_block_execfreq(bb, freq);
				}
			}
		}

		DEL_ARR_F(freqs);
	}

	/* Fallback solution: Use loop weight. */
	if (!valid_freq) {
		valid_freq = true;

		for (int idx = size - 1; idx >= 0; --idx) {
			ir_node       *bb    = (ir_node *) dfs_get_post_num_node(dfs, size - idx - 1);
			const ir_loop *loop  = get_irn_loop(bb);
			const int      depth = get_loop_depth(loop);
			double         freq  = 1.0;

			for (int d = 0; d < depth; ++d) {
				freq *= loop_weight;
			}

			/* Check for inf, nan and negative values. */
			if (isinf(freq) || !(freq >= 0)) {
				valid_freq = false;
				break;
			}
			set_block_execfreq(bb, freq);
		}
	}

	/* Fallback solution: All blocks have the same execution frequency. */
	if (!valid_freq) {
		for (int idx = size - 1; idx >= 0; --idx) {
			ir_node *bb = (ir_node *) dfs_get_post_num_node(dfs, size - idx - 1);
			set_block_execfreq(bb, 1.0);
		}
	}

	ir_free_resources(irg, IR_RESOURCE_BLOCK_VISITED
			  | IR_RESOURCE_IRN_VISITED
			  | IR_RESOURCE_IRN_LINK);

	dfs_free(dfs);
	DEL_ARR_F(lgs_to_mat);
	DEL_ARR_F(mat_to_lgs);
	free(in_fac);
	free(lgs_matrix);
	free(lgs_x);
}
