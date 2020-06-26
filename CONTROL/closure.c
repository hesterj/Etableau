#include <closure.h>

/*  Simple wrapper for branch contradiction testing
 *  Checks the label of tab for contradiction against the labels of its parents
*/

bool ClauseTableauBranchClosureRuleWrapper(ClauseTableau_p tab)
{
	Subst_p subst;
	assert(tab);
	assert(tab->label);
	bool leaf_regularity_checking = false;

	if ((subst = ClauseContradictsBranch(tab, tab->label)))
	{
		if (PStackGetSP(subst) == 0)  // Only subst needed was identity
		{
			SubstDelete(subst);
			return true;
		}
		else
		{
			ClauseTableauApplySubstitution(tab->master, subst);
			SubstDelete(subst);
			return true;
		}
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
	int num_branches_closed = 0;
	ClauseTableau_p open_branch = tableau->open_branches->anchor->succ;
	while (open_branch != tableau->open_branches->anchor)
	{
		if (ClauseTableauBranchClosureRuleWrapper(open_branch))
		{
			num_branches_closed += 1;
			open_branch->open = false;
			open_branch = open_branch->succ;
			TableauSetExtractEntry(open_branch->pred);
			if (open_branch == tableau->open_branches->anchor)
			{
				open_branch = open_branch->succ;
			}
			if (tableau->open_branches->members == 0)
			{
				return -num_branches_closed;
			}
		}
		else
		{
			open_branch = open_branch->succ;
		}
	}
	return num_branches_closed;
}

/*  Checks clause for contradiction against the nodes of tab
 *  Used to avoid allocating tableau children until we know there is a successful extension
 * 
*/

Subst_p ClauseContradictsBranch(ClauseTableau_p tab, Clause_p original_clause)
{
	assert(tab);
	assert(tab->label);
	Subst_p subst = NULL;
	Clause_p temporary_label;
	//ClauseSet_p unit_axioms = tab->master->unit_axioms;
	PStackPointer stack_pointer = 0;
	bool original_label_replaced = false;
	
	//long num_local_variables = 0;
	long num_local_variables = UpdateLocalVariables(tab);
	if (num_local_variables)
	{
		original_label_replaced = true;
		original_clause = ReplaceLocalVariablesWithFresh(tab, original_clause, tab->local_variables);
	}
	//num_local_variables = 0;
	
	//~ // Check against the unit axioms
	//~ Clause_p unit_handle = unit_axioms->anchor->succ;
	//~ Clause_p temporary_unit = unit_handle;
	//~ while (unit_handle != unit_axioms->anchor)
	//~ {
		//~ assert(unit_handle);
		//~ Clause_p tmp_unit_handle = ClauseCopyFresh(unit_handle, tab->master);
		//~ if ((subst = ClauseContradictsClause(tab, original_clause, tmp_unit_handle)))
		//~ {
			//~ tab->mark_int = 0; // Closing by a unit simulates an extension step
			//~ // Marking the root would case some leaves to be folded up too high in one step, unsound.
			//~ ClauseFree(tmp_unit_handle);
			//~ goto return_point;
		//~ }
		//~ ClauseFree(tmp_unit_handle);
		//~ unit_handle = unit_handle->succ;
	//~ }
	//fprintf(GlobalOut, "  Done.\n");
	
	// Check against the tableau AND its edges
	ClauseTableau_p temporary_tab = tab->parent;
	int distance_up = 1;
	while (temporary_tab)
	{
		if (num_local_variables == 0)
		{
			temporary_label = temporary_tab->label;
		}
		else
		{
			temporary_label = ReplaceLocalVariablesWithFresh(tab->master, temporary_tab->label, tab->local_variables);
		}
		if ((subst = ClauseContradictsClause(tab, temporary_label, original_clause)))
		{
			tab->mark_int = distance_up;
			if (num_local_variables)
			{
				ClauseFree(temporary_label);
			}
			goto return_point;
		}
		if (temporary_tab->folding_labels)
		{
			if ((subst = ClauseContradictsSet(temporary_tab, original_clause, temporary_tab->folding_labels, tab)))
			{
				//tab->mark_int = distance_up;
				if (tab->depth == distance_up)
				{
					tab->mark_int = distance_up;
				}
				else 
				{
					tab->mark_int = distance_up - 1; // Etableau reduction
				}
				if (num_local_variables)
				{
					ClauseFree(temporary_label);
				}
				goto return_point;
			}
		}
		if (num_local_variables)
		{
			ClauseFree(temporary_label);
		}
		distance_up += 1;
		temporary_tab = temporary_tab->parent;
	}
	
	return NULL;
	
	return_point: // Only accessed if a contradiction was found
	if (original_label_replaced)
	{
		ClauseFree(original_clause);
	}
	
	//fprintf(GlobalOut, "  Done with success.\n");
	return subst;
}

/*  Needs testing
*/

Subst_p ClauseContradictsSet(ClauseTableau_p tab, Clause_p leaf, ClauseSet_p set, ClauseTableau_p open_branch)
{
	assert(set->anchor);
	//~ //bool local_vars = false;
	// This IF statement has been disabled!!!
	if (NULL && (open_branch->local_variables) && (PStackGetSP(open_branch->local_variables) > 0))
	{
		fprintf(GlobalOut, "# Not allowed!!!\n");
		Clause_p handle = set->anchor->succ;
		Subst_p subst = NULL;
		while (handle != set->anchor)
		{
			Clause_p handle_clause = ReplaceLocalVariablesWithFresh(tab->master, handle, open_branch->local_variables);
			if ((subst = ClauseContradictsClause(tab, leaf, handle_clause)))
			{
				ClauseFree(handle_clause);
				return subst;
			}
			ClauseFree(handle_clause);
			handle = handle->succ;
		}
	}
	else // no local variables- easy situation
	{
		Clause_p handle = set->anchor->succ;
		Subst_p subst = NULL;
		while (handle != set->anchor)
		{
			if ((subst = ClauseContradictsClause(tab, leaf, handle)))
			{
				return subst;
			}
			handle = handle->succ;
		}
	}
	return NULL;
}

Subst_p ClauseContradictsSetSubst(ClauseTableau_p tab, Clause_p leaf, ClauseSet_p set, ClauseTableau_p open_branch, Subst_p subst)
{
	assert(set->anchor);
	Subst_p success_subst = NULL;
	//bool local_vars = false;
	PStackPointer stack_pointer = 0;
	if (PStackGetSP(open_branch->local_variables) > 0)
	{
		Clause_p handle = set->anchor->succ;
		//Subst_p subst = NULL;
		while (handle != set->anchor)
		{
			//Clause_p handle_clause = ReplaceLocalVariablesWithFresh(tab->master, handle, open_branch->local_variables);
			Clause_p handle_clause = ReplaceLocalVariablesWithFreshSubst(tab->master, handle, open_branch->local_variables, subst);
			if ((success_subst = ClauseContradictsClauseSubst(leaf, handle_clause, subst)))
			{
				ClauseFree(handle_clause);
				return subst;
			}
			ClauseFree(handle_clause);
			handle = handle->succ;
		}
	}
	else // no local variables- easy situation
	{
		Clause_p handle = set->anchor->succ;
		//Subst_p subst = NULL;
		while (handle != set->anchor)
		{
			Clause_p handle_clause = handle;
			if (PStackGetSP(open_branch->local_variables) > 0)
			{
			}
			//if ((subst = ClauseContradictsClause(tab, leaf, handle_clause)))
			if ((success_subst = ClauseContradictsClauseSubst(leaf, handle_clause, subst)))
			{
				return subst;
			}
			handle = handle->succ;
		}
	}
	return NULL;
}
