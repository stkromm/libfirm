#include "adt/array.h"
#include "assert.h"

#include "kaps.h"
#include "matrix.h"
#include "pbqp_edge.h"
#include "pbqp_edge_t.h"
#include "pbqp_node.h"
#include "pbqp_node_t.h"
#include "pbqp_t.h"

pbqp_edge *alloc_edge(pbqp *pbqp, int src_index, int tgt_index, matrix *costs)
{
	if (tgt_index < src_index) {
		return alloc_edge(pbqp, tgt_index, src_index, costs);
	}

	pbqp_edge *edge = obstack_alloc(&pbqp->obstack, sizeof(*edge));
	assert(edge);

	pbqp_node *src_node = get_node(pbqp, src_index);
	assert(src_node);
	edge->src = src_node;

	pbqp_node *tgt_node = get_node(pbqp, tgt_index);
	assert(tgt_node);
	edge->tgt = tgt_node;

	edge->costs = matrix_copy(pbqp, costs);

	/*
	 * Connect edge with incident nodes. Since the edge is allocated, we know
	 * that it don't appear in the edge lists of the nodes.
	 */
	ARR_APP1(pbqp_edge *, src_node->edges, edge);
	edge->src = src_node;
	ARR_APP1(pbqp_edge *, tgt_node->edges, edge);
	edge->tgt = tgt_node;

	return edge;
}
