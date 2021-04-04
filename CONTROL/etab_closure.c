#include <etab_closure.h>
#include <etab_backtrack.h>

/*  Simple wrapper for branch contradiction testing
 *  Checks the label of tab for contradiction against the labels of its parents
*/

bool ClauseTableauBranchClosureRuleWrapper(ClauseTableau_p tab)
{
	Subst_p subst;
	assert(tab);
	assert(tab->label);
	assert(tab->label->set);

	//if ((subst = ClauseContradictsBranch(tab, tab->label)))
	if ((subst = ClauseContradictsBranchSimple(tab, tab->label)))
	{
		if (SubstIsFailure(tab, subst))
		{
			tab->id = 0; // ClauseContradictsBranch sets tab->id, if we block the closure rule attempt that needs to be reset to 0.
			tab->mark_int = 0; // Similarly, the mark_int is set.  This needs to be undone...
			//fprintf(GlobalOut, "# Failure substitution in closure rule attempt!\n");
			SubstDelete(subst);
			return false;
		}

		Backtrack_p backtrack = BacktrackAlloc(tab, subst, 0, CLOSURE_RULE);
		assert(BacktrackIsClosureStep(backtrack));
		assert(tab->arity == 0);
		PStackPushP(tab->backtracks, backtrack);
		PStack_p position_copy = PStackCopy(backtrack->position);
		PStackPushP(tab->master->master_backtracks, position_copy);


		ClauseTableauApplySubstitution(tab->master, subst);
		assert(tab->set == tab->open_branches);
		tab->open = false;
		TableauSetExtractEntry(tab);
		// Check for regularity?
		if (!ClauseTableauIsLeafRegular(tab->master))
		{
			//fprintf(GlobalOut, "# Backtracking after closure step violated regularity\n");
			__attribute__((unused)) bool backtracked = BacktrackWrapper(tab->master);
			assert(backtracked);
			assert(tab->mark_int == 0);
			assert(tab->id == 0);
			SubstDelete(subst);
			return false;
		}
		assert(tab->info);
		//tab->folding_blocked = true;
		backtrack->completed = true;
		//tab->mark_int = tab->depth;
		SubstDStrPrint(tab->info, subst, tab->terms->sig, DEREF_NEVER);
		DStrAppendStr(tab->info, " Reduction step with clause ");
		DStrAppendInt(tab->info, tab->id);
		DStrAppendStr(tab->info, " ");
		SubstDelete(subst);
		ClauseTableauRegisterStep(tab);
		assert(tab->label->set);
		backtrack->completed = true;
		return true;
	}
	return false;
}

/*
 *  Attempt closure rule on all the open branches of the tableau.
 *  Returns the total number of closures that were accomplished.
 *  If there are no more open branches (a closed tableau was found),
 *  return the negative of the total number of branches closed.
 * 
 *  
*/


int AttemptClosureRuleOnAllOpenBranches(ClauseTableau_p tableau)
{
	assert(tableau);
	assert(tableau->master);
	assert(tableau->master->label);
	int num_branches_closed = 0;
	ClauseTableau_p open_branch = tableau->open_branches->anchor->succ;
	assert(open_branch);
	while (open_branch != tableau->open_branches->anchor)
	{
		ClauseTableau_p next_open_branch = open_branch->succ;
		assert(open_branch);
		assert(next_open_branch);
		if (ClauseTableauBranchClosureRuleWrapper(open_branch))
		{
			assert(PStackGetSP(open_branch->backtracks));
			num_branches_closed += 1;
			open_branch = next_open_branch;
			assert(open_branch);
			if (open_branch == tableau->open_branches->anchor)
			{
				break;
			}
			if (tableau->open_branches->members == 0)
			{
				return -num_branches_closed;
			}
		}
		else
		{
			assert(open_branch->id == 0);
			open_branch = next_open_branch;
		}
	}
	return num_branches_closed;
}

/*  Checks clause for contradiction against the nodes of tab
 *  This is a version of ClauseContradictsBranch that does not deal with local variables.
 *
*/

Subst_p ClauseContradictsBranchSimple(ClauseTableau_p open_branch, Clause_p original_clause)
{
	assert(open_branch);
	assert(open_branch->label);
	assert(original_clause->set);
	assert(NodeIsLeaf(open_branch));
	Subst_p subst = NULL;
	Clause_p temporary_label = NULL;

	ClauseTableauUpdateVariables(open_branch->master);

#ifdef LOCAL
	//assert(open_branch->local_variables);
	UpdateLocalVariables(open_branch);
#endif

	// Check against the unit axioms
	ClauseSet_p unit_axioms = open_branch->master->unit_axioms;
	assert(unit_axioms);
	Clause_p unit_handle = unit_axioms->anchor->succ;
	while (unit_handle != unit_axioms->anchor)
	{
		assert(unit_handle);
		Clause_p tmp_unit_handle = ClauseCopyFresh(unit_handle, open_branch->master);
		if ((subst = ClauseContradictsClause(open_branch, original_clause, tmp_unit_handle)))
		{
			open_branch->mark_int = open_branch->depth;
			open_branch->id = ClauseGetIdent(unit_handle);
			// Marking the root would case some leaves to be folded up too high in one step, unsound.
			ClauseFree(tmp_unit_handle);
			goto return_point;
		}
		ClauseFree(tmp_unit_handle);
		unit_handle = unit_handle->succ;
	}

	// Check against the tableau AND its edges
	ClauseTableau_p temporary_tab = open_branch->parent;
	int distance_up = 1;
	while (temporary_tab)
	{
		temporary_label = temporary_tab->label;
		if ((subst = ClauseContradictsClause(open_branch, temporary_label, original_clause)))
		{
			open_branch->mark_int = distance_up;
			open_branch->id = ClauseGetIdent(temporary_tab->label);
			goto return_point;
		}

		// Now we check the original clause against the folding labels of the node we are at.
		if (temporary_tab->folding_labels)
		{
			if ((subst = ClauseContradictsSetSimple(temporary_tab, original_clause, temporary_tab->folding_labels, open_branch)))
			{
				DStrAppendStr(open_branch->info, " Fold. ");
				open_branch->mark_int = distance_up;
				goto return_point;
			}
		}
		distance_up += 1;
		temporary_tab = temporary_tab->parent;
	}

	return_point:
	return subst;
}


/*
** As ClauseContradictsSet, but does not deal with local variables at all.
*/

Subst_p ClauseContradictsSetSimple(ClauseTableau_p tab, Clause_p leaf, ClauseSet_p set, ClauseTableau_p open_branch)
{
	assert(tab);
	assert(set->anchor);
	assert(open_branch);
	assert(leaf);
	assert(NodeIsLeaf(open_branch));
	Subst_p subst = NULL;

	Clause_p handle = set->anchor->succ;
	while (handle != set->anchor)
	{
		if ((subst = ClauseContradictsClause(open_branch, leaf, handle)))
		{
			open_branch->id = ClauseGetIdent(handle);
			return subst;
		}
		handle = handle->succ;
	}

	return subst;
}

//Subst_p ClauseContradictsSetSubst(ClauseTableau_p tab, Clause_p leaf, ClauseSet_p set, ClauseTableau_p open_branch, Subst_p subst)
//{
	//assert(set->anchor);
	//Subst_p success_subst = NULL;
	//if (PStackGetSP(open_branch->local_variables) > 0)
	//{
		//Clause_p handle = set->anchor->succ;
		//while (handle != set->anchor)
		//{
			////Clause_p handle_clause = ReplaceLocalVariablesWithFresh(tab->master, handle, open_branch->local_variables);
			//Clause_p handle_clause = ReplaceLocalVariablesWithFreshSubst(tab->master, handle, open_branch->local_variables, subst);
			//if ((success_subst = ClauseContradictsClauseSubst(leaf, handle_clause, subst)))
			//{
				//ClauseFree(handle_clause);
				//return subst;
			//}
			//ClauseFree(handle_clause);
			//handle = handle->succ;
		//}
	//}
	//else // no local variables- easy situation
	//{
		//Clause_p handle = set->anchor->succ;
		////Subst_p subst = NULL;
		//while (handle != set->anchor)
		//{
			//Clause_p handle_clause = handle;
			//if (PStackGetSP(open_branch->local_variables) > 0)
			//{
			//}
			////if ((subst = ClauseContradictsClause(tab, leaf, handle_clause)))
			//if ((success_subst = ClauseContradictsClauseSubst(leaf, handle_clause, subst)))
			//{
				//return subst;
			//}
			//handle = handle->succ;
		//}
	//}
	//return NULL;
//}
