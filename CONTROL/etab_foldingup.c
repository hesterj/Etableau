#include "etab_foldingup.h"

/*  Returns true if all of the nodes below tableau are closed
 *  Closes nodes that have all children closed
*/

void assert_all_children_closed(ClauseTableau_p tab);

void assert_all_children_closed(ClauseTableau_p tab)
{
	assert(tab->open == false);
	for (short i=0; i<tab->arity; i++)
	{
		assert(tab->children[i]->set == NULL);
		assert_all_children_closed(tab->children[i]);
	}
}

bool ClauseTableauMarkClosedNodes(ClauseTableau_p tableau, int *subtree_saturation_closed)
{
	//printf("Attempting to mark a new node.");
	int saturation_closed = *subtree_saturation_closed;
	assert(tableau);
	if (tableau->set)
	{
		//printf("Found an open branch while attempting to mark nodes as closed.\n");
		return false;
	}
	if (tableau->saturation_closed)
	{
		//fprintf(GlobalOut, "# Found saturation closed branch by marking\n");
		assert(tableau->open == false);
		saturation_closed = CHILD_CLOSED_BY_SATURATION;
	}
	int arity = tableau->arity;
	//if (arity == 0)
	//{
		//return false;
	//}
	bool all_children_closed = true;
	// Check to see if all the children are actually superclosed
	//printf("Marking children.\n");
	for (int i = 0; i < arity; i++)
	{
			assert(tableau->children[i]);
			ClauseTableau_p child = tableau->children[i];
			bool child_is_superclosed = ClauseTableauMarkClosedNodes(child, &saturation_closed);
#ifndef NDEBUG
			if (child_is_superclosed)
			{
				assert_all_children_closed(child);
			}
#endif
			if (!child_is_superclosed) // there is a child that is open or whose children are open
			{
				all_children_closed = false;
			}
	}
	if (all_children_closed)
	{
		//printf("all children closed, arity %d\n", tableau->arity);
		tableau->open = false;
		return true;
	}
	else
	{
		tableau->open = true;
		return false;
	}
	return true;
}

/*  Iterate through the nodes collected in stack,
 *  return the deepest one.
*/

ClauseTableau_p PStackGetDeepestTableauNode(PStack_p stack)
{
	int deepest_depth = 0;
	ClauseTableau_p deepest = NULL;
	//printf("Stack pointer in finding deepest: %ld\n", PStackGetSP(stack));
	if (PStackEmpty(stack))
	{
		printf("Error: Trying to find deepest node of empty stack!\n");
		printf("PStackGetDeepestTableauNode\n");
		exit(0);
	}
	for (PStackPointer p=0; p<PStackGetSP(stack); p++)
	{
		ClauseTableau_p temp = PStackElementP(stack, p);
		//printf("Depth of temp: %d\n", temp->depth);
		if (temp->depth >= deepest_depth)
		{
			//printf("d%d\n", temp->depth);
			deepest = temp;
			deepest_depth = deepest->depth;
		}
	}
	return deepest;
}

/*  marks are the integer distance from a node to the dominating node it was closed with
 *  Returns the clause labelling the mark'd node.
*/

Clause_p FoldingUpGetLabelFromMark(ClauseTableau_p tableau, int mark)
{
	while (mark)
	{
		tableau = tableau->parent;
		mark -= 1;
	}
	return tableau->label;
}

/*  Integer marks represent the distance up used for contradiction.
 *  This returns the node at mark distance up from tableau.
*/

ClauseTableau_p FoldingUpGetNodeFromMark(ClauseTableau_p tableau, int mark)
{
	while (mark)
	{
		tableau = tableau->parent;
		mark -= 1;
	}
	return tableau;
}

/*  Insert the clause in to the edge.
 *  If nothing has been folded up to this edge yet (edge is NULL),
 *  then allocate a clause set for insertion.
*/

void ClauseTableauEdgeInsert(ClauseTableau_p edge, Clause_p clause)
{
	if (edge->folding_labels)
	{
		ClauseSetInsert(edge->folding_labels, clause);
	}
	else 
	{
		edge->folding_labels = ClauseSetAlloc();
		ClauseSetInsert(edge->folding_labels, clause);
	}
}

/*  Simple wrapper for CollectDominatedMarkings.
 *  Returns a stack of pointers to the markings of nodes dominated by "tableau"
 *  The first parameter is kept as the first node we are calling this function from.
*/

PStack_p CollectDominatedMarkingsWrapper(ClauseTableau_p tableau)
{
	PStack_p dominated_markings = PStackAlloc();
	CollectDominatedMarkings(tableau, tableau, dominated_markings);
	//printf("# Done collecting markings\n");
	return dominated_markings;
}

/*  For all of the nodes below tableau, collect the markings in to 
 *  the stack.  
 *  Used for folding up, all of the branches below
 *  should have a marking at the leaf, as they have been closed by an extension 
 *  step or a closure (reduction) rule.
 * 
 *  The original node is kept track of to ensure that we only add markings of 
 *  dominated nodes that are above the original node.  Otherwise,
 *  any node closed by an extension step cannot be folded up as it has a 
 *  mark_int of 1.
*/


void CollectDominatedMarkings(ClauseTableau_p original, ClauseTableau_p tableau, PStack_p stack)
{
	if (tableau->mark_int > 0)
	{
		//assert(NodeIsLeaf(tableau));
		//printf("Mark int of a leaf node dominated by the tableau: %d\n", tableau->mark_int);
		ClauseTableau_p mark = FoldingUpGetNodeFromMark(tableau, tableau->mark_int);
		if (mark->depth <= original->depth)
		{
			//printf("# mark of depth %d\n", mark->depth);
			PStackPushP(stack, mark);
		}
	}
	for (int i=0; i<tableau->arity; i++)
	{
		CollectDominatedMarkings(original, tableau->children[i], stack);
	}
}

/*  From the stack of nodes "marks", collect the ones that dominate
 *  the tableau node "tableau"
 * 
*/

PStack_p NodesThatDominateTableauFromMarks(ClauseTableau_p tableau, PStack_p marks)
{
	PStack_p dominating_nodes = PStackAlloc();
	for (PStackPointer p = 0; p<PStackGetSP(marks); p++)
	{
		ClauseTableau_p mark = PStackElementP(marks, p);
		//printf("mark depth in nodes that dominate tableau from marks: %d\n", mark->depth);
		if (TableauDominatesNode(mark, tableau))
		{
			//printf("added\n");
			PStackPushP(dominating_nodes, mark);
		}
	}
	//printf("Number of dominating nodes from marks: %ld\n", PStackGetSP(dominating_nodes));
	return dominating_nodes;
}

/*  Follow the folding up rule from Handbook of Automated Reasoning Vol. 2
 *  Returns the number of nodes the label was folded up, 
 *  returns 0 if not able to fold up.
 * 
 *  If the node has already been folded up to the eligible node, or one lower,
 *  the node will not be folded up and 0 will be returned.
*/

int FoldUpAtNode(ClauseTableau_p node)
{
	assert(node);
	ClauseTableau_p master_node = node->master;
	assert(node->label);
	assert(master_node->folding_labels);
	assert(node->folding_labels);

	// Do not fold up the master node
	if (node->depth == 0) return 0;
	// Do not fold up leaf nodes
	if (NodeIsLeaf(node)) return 0;
	// Do not fold up nodes that were previously leaves
	//if (node->folding_blocked)
	if (ClauseTableauQueryProp(node, TUPFoldingBlocked))
	{
		//printf("# blocked bad fold\n");
		//fflush(stdout);
		return 0;
	}
	// Do not fold up nodes that are not superclosed

	int child_saturation_closed = NO_CHILDREN_CLOSED_BY_SATURATION;
	if (!ClauseTableauMarkClosedNodes(node, &child_saturation_closed))
	{
		//printf("Attempted to fold up nonclosed node, returning 0 in FoldUpAtNode\n");
		return 0;
	}

	assert(ClauseLiteralNumber(node->label) == 1);

	//Easy situation- if the node has already been folded up to the root do nothing
	if (node->folded_up == node->depth)
	{
		//printf("Node has already been folded up to root.\n");
		return 0;
	}
#ifndef NDEBUG
	assert_all_children_closed(node);
#endif

	// Get the nodes that are eligible to fold up to
	PStack_p dominated_markings = CollectDominatedMarkingsWrapper(node);
	// This may not be necessary, the markings of dominated nodes must come from the same branch?
	PStack_p dominators = NodesThatDominateTableauFromMarks(node, dominated_markings); 
	PStackFree(dominated_markings);

	if (child_saturation_closed == CHILD_CLOSED_BY_SATURATION)
	{
		// A superclosed node with children closed by saturation could have had any clause on the branch used in its closing
		// To reflect this, the deepest relevant node (node itself here) must be included as a dominator.
		// By keeping track of which clauses were used in the saturation attempt, it could potentially be folded up higher.
		// This would be tricky to implement and likely not worth the effort...
		PStackPushP(dominators, node);
	}
	
	Clause_p flipped_label = NULL;
	if ((PStackGetSP(dominators) == 0) ||
		((PStackGetSP(dominators) == 1) && (PStackElementP(dominators,0) == node->master)))
	{
		// Case 1: Add the negation of the label of node to the literals at the root (node->master)
		if (node->folded_up != node->depth) // Make sure we have not already folded to the root
		{
			flipped_label = ClauseCopy(node->label, node->terms);
			ClauseFlipLiteralSign(flipped_label, flipped_label->literals);
			node->folded_up = node->depth;
			ClauseTableauEdgeInsert(master_node, flipped_label);
			//ClauseSetInsertSet(master_node->folding_labels, node->folding_labels);
			ClauseSetDeleteCopies(master_node->folding_labels);
			node->folded_up = node->depth;
			//fprintf(stdout, "Folding up clause %ld to the root\n", ClauseGetIdent(flipped_label));

			//ClauseFree(flipped_label); // Temporary, for debugging
		}
	}
	else
	{
		// Case 2: Get the deepest path node, add the negation of the label of the node to the parent of deepest
		ClauseTableau_p previous_fold = FoldingUpGetNodeFromMark(node, node->folded_up);
		ClauseTableau_p deepest = PStackGetDeepestTableauNode(dominators);
		assert(deepest);
		if ((node->folded_up != 0)   // Doesn't matter if the node has not been folded up yet
			  && (deepest->depth <= previous_fold->depth))
		{
			// This node has already been folded up to the node deepest, or one higher, do nothing
		}
		else if (!(deepest->parent))
		{
			//  We are at the master node, probably because of unit axioms... fold up to it
			//printf("Folding up to master node.\n");
			flipped_label = ClauseCopy(node->label, node->terms);
			ClauseFlipLiteralSign(flipped_label, flipped_label->literals);
			//printf("The flipped literal clause that has been folded up to root:\n");
			//ClausePrint(GlobalOut, flipped_label, true);printf("\n");
			node->folded_up = node->depth;
			ClauseTableauEdgeInsert(master_node, flipped_label);
			//ClauseSetInsertSet(master_node->folding_labels, node->folding_labels);
			ClauseSetDeleteCopies(master_node->folding_labels);
			//fprintf(stdout, "Folding up clause %ld case 2.1\n", ClauseGetIdent(flipped_label));
			//ClauseFree(flipped_label); // Temporary, for debugging
		}
		else
		{
			// The actual case 2
			assert(deepest->depth > 0);
			node->folded_up = ClauseTableauDifference(deepest, node)+1;
			//assert(deepest != node);
			assert(node->folded_up);
			flipped_label = ClauseCopy(node->label, node->terms);
			//if (ClauseGetIdent(flipped_label) == 100981)
			//{
				//fprintf(stdout, "# Folding up the bastard\n");
				//if (ClauseContradictsSet(node, flipped_label, node->master->unit_axioms, node))
				//{
					//fprintf(stdout, "# Contradicts unit axioms...\n");
				//}
				//fflush(stdout);
			//}
			ClauseFlipLiteralSign(flipped_label, flipped_label->literals);
			ClauseTableauEdgeInsert(deepest->parent, flipped_label);
			//ClauseSetInsertSet(deepest->parent->folding_labels, node->folding_labels);
			ClauseSetDeleteCopies(deepest->parent->folding_labels);
			//fprintf(stdout, "Folding up clause %ld case 2.2, deepest depth is %d\n", ClauseGetIdent(flipped_label), deepest->depth);
			//ClauseFree(flipped_label); // Temporary, for debugging
		}
		
	}
	
	PStackFree(dominators);
	return node->folded_up;
}

/*
 * Folds up the entire tableau- attempting to fold up at every node below, and including, tableau.
 * Does not fold up edges.
 * 
 * Returns (sum of distances folded) of the number of nodes that were successfully folded up.
*/


int FoldUpEveryNodeOnce(ClauseTableau_p tableau)
{
	int number_of_nodes_folded = 0;
	number_of_nodes_folded += FoldUpAtNode(tableau);
	for (int i=0; i<tableau->arity; i++)
	{
		number_of_nodes_folded += FoldUpEveryNodeOnce(tableau->children[i]);
	}
	return number_of_nodes_folded;
}

/*
 * This method attempts to fold up all the nodes of a tableau,
 * and then tries to use closure/reduction rule on the open branches of
 * the tableau.  If any closure steps were done, try to fold up 
 * every node again and close the remaining open branches.  
 * If all the nodes were folded up and no new closures are possible, 
 * return the total number of closures accomplished.
 * 
 * If a closed tableau was found, return the negative of the total 
 * number of closures accomplished.  This means there is a closed
 * tableau, which is proof success.
*/

int FoldUpCloseCycle(ClauseTableau_p tableau)
{
	int total_closures_done = 0;
	int closures_done = 0;
	int folding_ups_done = 0;
	do
	{
		closures_done = 0;
#ifdef FOLD
		folding_ups_done += FoldUpEveryNodeOnce(tableau);
#endif
		closures_done = AttemptClosureRuleOnAllOpenBranches(tableau);
		total_closures_done += closures_done;
		//printf("Closures done in FoldUpCloseCycle: %d\n", closures_done);
		if ((tableau->open_branches->members == 0) || (closures_done < 0))
		{
			assert(tableau->open_branches->members == 0);
			fprintf(GlobalOut, "# Closed tableau found in foldup close cycle with %d folds.\n", folding_ups_done);
			return -total_closures_done;
		}
	} while (closures_done > 0);
	//fprintf(GlobalOut, "# %d closures done\n", total_closures_done);
	return total_closures_done;
}

