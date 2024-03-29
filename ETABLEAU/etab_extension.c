#include "etab_extension.h"

bool extension_is_strong(ClauseTableau_p parent,
						 ClauseTableau_p grandparent,
						 ClauseSet_p new_leaf_clauses,
						 Clause_p head_literal);

TableauExtension_p TableauExtensionAlloc(Clause_p selected,
										 Subst_p subst, 
										 Clause_p head_clause, 
										 ClauseSet_p other_clauses, 
										 ClauseTableau_p parent,
										 long head_lit_position)
{
	TableauExtension_p handle = TableauExtensionCellAlloc();
	handle->selected = selected;
	handle->subst = subst;
	handle->head_clause = head_clause;
	handle->other_clauses = other_clauses;
	handle->parent = parent;
	handle->succ = NULL;
	handle->head_lit_position = head_lit_position;
	return handle;
}

/*  Does not free all objects pointed to.  For use after an extension step has been done.
 * 
*/

void TableauExtensionFree(TableauExtension_p ext)
{
	TableauExtensionCellFree(ext);
}

ClauseSet_p ClauseStackToClauseSet(ClauseStack_p stack)
{
	PStackPointer number_of_clauses = PStackGetSP(stack);
	ClauseSet_p clauses = ClauseSetAlloc();
	for (PStackPointer i=0; i<number_of_clauses; i++)
	{
		Clause_p clause = PStackElementP(stack, i);
		if (clause->set)
		{
			ClauseSetExtractEntry(clause);
		}
		ClauseSetInsert(clauses, clause);
	}
	return clauses;
}

ClauseSet_p SplitClauseFresh(TB_p bank, ClauseTableau_p tableau, Clause_p clause)
{
	Eqn_p lit = NULL;
	Clause_p leaf_clause = NULL;
	assert(clause);
	assert(tableau);
	ClauseSet_p set = ClauseSetAlloc();
	Clause_p fresh_clause = ClauseCopyFresh(clause, tableau);

	//printf("splitclausefresh\n");
	//clauseprint(clause);
	//clauseprint(fresh_clause);

	EqnRef literals_ref = &(fresh_clause->literals);
	while (*literals_ref)
	{
		lit = EqnListExtractFirst(literals_ref);
		leaf_clause = ClauseAlloc(lit);
		ClauseSetInsert(set, leaf_clause);
	}
	ClauseFree(fresh_clause);
	return set;
}

/*  Do all of the extension rules possible with the selected clause.
 *  There may be multiple literals extension can be done with.
 *  The resulting tableaux are added to distinct_tableaux, if new_tableaux is passed.
 *  At the end, when all of the new tableaux are created, the original tableau is removed from
 *  distinct_tableaux.
 *  Otherwise, if new_tableaux is not passed, the extension is done directly on to the branch.
*/

int ClauseTableauExtensionRuleAttemptOnBranch(TableauControl_p tableau_control,
											  ClauseTableau_p open_branch,
											  TableauSet_p distinct_tableaux,
											  Clause_p selected,
											  TableauStack_p new_tableaux)
{
	ClauseTableau_p master = open_branch->master;
	int extensions_done = 0;
	int subst_completed = 0;
	bool folding_extension = false;


	//ClauseTableauUpdateVariablesArray(open_branch->master);
	ClauseTableauUpdateVariablesArray2(open_branch->master);

	ClauseSet_p new_leaf_clauses = SplitClauseFresh(open_branch->terms, master, selected);
	assert(new_leaf_clauses->members);
	assert(new_leaf_clauses->members > 1);
	assert(open_branch->folding_labels);

	Clause_p folding_iterator = open_branch->folding_labels->anchor->succ;
	Clause_p open_branch_label = open_branch->label;
	Clause_p leaf_clause = new_leaf_clauses->anchor->succ;
	long position = 0; // This is the position of the current leaf clause in the split clause
	restart: while (leaf_clause != new_leaf_clauses->anchor)
	{
		assert(open_branch);
		assert(open_branch != open_branch->open_branches->anchor);
		assert(open_branch->parent);
		assert(open_branch->label);
		assert(open_branch->label->set);
		assert(open_branch->arity == 0);
		assert(open_branch_label);
		assert(open_branch->label->set); // Labels are supposed to be part of a collection of clauses for GC purposes
		assert(leaf_clause);
		assert(leaf_clause->literals);
		assert(open_branch_label->literals);
		assert(master->label);
		assert(selected);

		Subst_p subst = NULL;

		// Here we are only doing the first possible extension- need to create a list of all of the extensions and do them...
		// The subst, leaf_clause, new_leaf_clauses, will have to be reset, but the open_branch can remain the same since we have not affected it.
		if ((subst = ClauseContradictsClause(open_branch, leaf_clause, open_branch_label))) // stricter extension step
		{
			ClauseTableau_p extended = NULL;
			Clause_p head_clause = leaf_clause;
			if (!extension_is_strong(open_branch,
									 open_branch->parent,
									 new_leaf_clauses,
									 head_clause))
			{
				SubstDelete(subst);
				// we're continuing to the next leaf clause
			}
			else
			{
				subst_completed++;
				TableauExtension_p extension_candidate = TableauExtensionAlloc(selected,
																			   subst,
																			   head_clause,
																			   new_leaf_clauses,
																			   open_branch,
																			   position);
				// If there is no new_tableaux stack passed to the function we are in, the extension is done on the tableau itself
				extended = ClauseTableauExtensionRuleWrapper(tableau_control,
															 extension_candidate,
															 new_tableaux);
				TableauExtensionFree(extension_candidate);

				if (extended) // extension may not happen due to regularity
				{
					if (folding_extension)
					{
						printf("Folding extension!\n");
						fflush(stdout);
					}
					extensions_done++;
					tableau_control->number_of_extensions++;
					if (tableau_control->branch_saturation_enabled)
					{
						CloseBranchesWithEprover(tableau_control, extended->master, 10000);
					}
					if (LIKELY(!new_tableaux)) // If the tableau has been extended on, we must go back and select another branch
					{
						goto return_point;
					}
				}
			}
		}
		position++;
		leaf_clause = leaf_clause->succ;
	}
#ifdef EXTEND_WITH_FOLDING_LABELS
	if (folding_iterator != open_branch->folding_labels->anchor->succ)
	{
		folding_extension = true;
		open_branch_label = folding_iterator;
		leaf_clause = new_leaf_clauses->anchor->succ;
		position = 0; // This is the position of the current leaf clause in the split clause
		folding_iterator = folding_iterator->succ;
		goto restart;
	}
#endif

	//  OK We're done
	return_point:
	ClauseSetFree(new_leaf_clauses);
	return extensions_done;
}

/*  Do an extension rule attempt, only way it can fail is through regularity.
**  Does not create a copy of the tableau, actually extends the tableau passed to it.
**  The ClauseTableau_p parent is the node that is extended upon, always with multiple branches.
**
**  Important:  When this function is called, there is a substitution active.
*/

ClauseTableau_p ClauseTableauExtensionRuleNoCopy(TableauControl_p tableaucontrol,
												 TableauExtension_p extension)
{
	Subst_p subst = extension->subst;
	if (ExtensionIsFailure(extension->parent, subst, ClauseGetIdent(extension->selected), extension->head_lit_position))
	{
		ETAB_VERBOSE(printf("# Extension is blocked due to being a failure extension\n");)
		SubstDelete(subst);
		return NULL;
	}
	ClauseTableau_p parent = extension->parent;
	ClauseTableau_p master = parent->master;
	TB_p bank = extension->parent->terms;
	Sig_p sig = master->terms->sig;
	Clause_p head_literal_clause = NULL;
	master->active_branch = NULL; // We have the handle where we are working, so set this to NULL to indicate this.

	assert(extension->parent->id == 0);
	assert(master->parent == NULL);
	assert(parent);
	assert(parent->arity == 0);
	assert(parent->children == NULL);
	assert(master->open_branches);
	assert(master->open_branches->members != 0);
	assert(extension->selected);
	assert(master->state);
	assert(master->control);
	assert(master->open_branches);
	assert(master->backtracks);
	assert(master->failures);
	assert(parent != parent->master);
	assert(parent->set == parent->open_branches);

	/*
	**  If this extension has already been performed at this node and failed, it must be prevented.
	*/


	ClauseTableauApplySubstitution(master, subst);
	TableauSetExtractEntry(parent); // Remove the parent from the collection of open branches
	parent->id = ClauseGetIdent(extension->selected);

	// Register the extension step that we are about to do with stack of backtracks we have available to us.

	Backtrack_p backtrack = BacktrackAlloc(parent, subst, extension->head_lit_position, EXTENSION_RULE);
	PStackPushP(parent->backtracks, backtrack);
	PStack_p position_copy = PStackCopy(backtrack->position);
	PStackPushP(parent->master->master_backtracks, position_copy);

	ClauseSet_p new_leaf_clauses_set = ClauseSetAlloc(); // Copy the clauses of the extension into this


	// This for loop is used for regularity checking.  If the extension would create an irregular branch, block it and return NULL.
	for (Clause_p handle = extension->other_clauses->anchor->succ;
		 handle != extension->other_clauses->anchor;
		 handle = handle->succ)
	{
		Clause_p subst_applied = EtableauClauseCopy(handle, bank, NULL);
		ClauseSetInsert(new_leaf_clauses_set, subst_applied);
		//if (ClauseTableauBranchContainsLiteral(parent, handle->literals))
		if (ClauseTableauBranchContainsLiteral(parent, subst_applied->literals))
		{
			ETAB_VERBOSE(printf("# Irregular extension stopped at parent\n");)
			ClauseSetFree(new_leaf_clauses_set);
			SubstDelete(subst); // If the extension is irregular, delete the substitution and return NULL.
			__attribute__((unused)) bool backtracked = BacktrackWrapper(master, BacktrackReasonIrregularExtension);
			assert(backtracked);
			return NULL;  // REGULARITY CHECKING!
		}
		if (extension->head_clause == handle)
		{
			head_literal_clause = subst_applied;
		}
	}

	// At this point, parent has NOT been extended on, so the only way an irregularity can happen is if the OTHER open branches contain one.
	// They have had their labels replaced, and parent is no longer in the open branches set, so we check the remaining open branches.
	if (!ClauseTableauIsLeafRegular(master))
	{
		ETAB_VERBOSE(fprintf(GlobalOut, "# Irregular extension stopped at non-parent\n");)
		ClauseSetFree(new_leaf_clauses_set);
		SubstDelete(subst); // If the extension is irregular, delete the substitution and return NULL.
		__attribute__((unused)) bool backtracked = BacktrackWrapper(master, BacktrackReasonIrregularExtension);
		assert(backtracked);
		return NULL;  // REGULARITY CHECKING!

	}
	backtrack->completed = true; // The extension is happening at this point.

	long number_of_children = new_leaf_clauses_set->members;

	assert(head_literal_clause);
	assert(number_of_children == extension->other_clauses->members);
	assert(number_of_children > 1);
	assert(head_literal_clause->set == new_leaf_clauses_set);

	parent->children = ClauseTableauArgArrayAlloc(number_of_children);
	Clause_p leaf_clause = NULL;
	// Create children tableau for the leaf labels.  The head literal is labelled as closed.
	for (long p=0; p < number_of_children; p++)
	{
		leaf_clause = ClauseSetExtractFirst(new_leaf_clauses_set);
		parent->children[p] = ClauseTableauChildLabelAlloc(parent, leaf_clause, p);
		assert(leaf_clause);
		assert(parent->children[p]->label);
		assert(parent->children[p]->label->set);
		if (leaf_clause == head_literal_clause)
		{
			parent->children[p]->open = false;
			parent->children[p]->mark_int = 1;
			parent->children[p]->head_lit = true;
		}
		else
		{
			TableauSetInsert(parent->open_branches, parent->children[p]);
			parent->children[p]->open = true;
		}
	}
	assert(ClauseSetEmpty(new_leaf_clauses_set));
	assert(number_of_children == parent->arity);


	ClauseSetFree(new_leaf_clauses_set);
	// Now that the parent has been extended on, it should be removed from the collection of open leaves.
	// Important to do this now, as otherwise folding up or branch saturation may not work correctly.


	// The copying is done, we can delete the subst and print it to the info
	DStrAppendStr(parent->info, " Expansion with clause ");
	DStrAppendInt(parent->info, parent->id);
	DStrAppendStr(parent->info, " ");
	SubstDStrPrint(parent->info, subst, sig, DEREF_NEVER);
	ClauseTableauRegisterStep(parent);


	SubstDelete(subst); // Extremely important.  The backtracks require information from the substitution.

	// The work is done- try to close the remaining branches

	FoldUpCloseCycle(parent->master);

	// The parent may have been completely closed and extracted
	// from the collection of open branches during the foldup close
	// cycle, or during E saturation proof search on a local branch.

	if (parent->open_branches->members == 0)
	{
		tableaucontrol->closed_tableau = parent->master;
	}
	assert(PStackGetSP(parent->backtracks));

	ETAB_VERBOSE(printf("# Extension completed\n");)
	// There is no need to apply the substitution to the tablaeu, it has already been done by copying labels.
	// In fact, the substitution should be free'd before this function ever returns.
	return parent->master;
}

/*  Do an extension rule attempt, only way it can fail is through regularity.
**  Create a copy of the tableau and extend on it, original is unmolested
**  The ClauseTableau_p parent is the node that is extended upon, always with multiple branches.
**
**  Important:  When this function is called, there is a substitution active.
*/

ClauseTableau_p ClauseTableauExtensionRuleCopy(TableauControl_p tableaucontrol,
											   TableauStack_p new_tableaux,
											   TableauExtension_p extension)
{

	/*
	**  If this extension has already been performed at this node and failed, it must be prevented.
	*/
	Subst_p subst = extension->subst;
	if (ExtensionIsFailure(extension->parent, subst, ClauseGetIdent(extension->selected), extension->head_lit_position))
	{
		//fprintf(GlobalOut, "# Failure substitution in extension!\n");
		SubstDelete(subst);
		return NULL;
	}

	ClauseTableau_p old_parent = extension->parent;
	ClauseTableau_p old_master = old_parent->master;
	TB_p bank = extension->parent->terms;
	Sig_p sig = old_master->terms->sig;
	Clause_p head_literal_clause = NULL;
	old_master->active_branch = old_parent; // We have the handle where we are working, so set this to NULL to indicate this.
	assert(old_parent->label);
	assert(old_parent->label->set);

	ClauseTableau_p master = ClauseTableauMasterCopy(old_master);
	ClauseTableau_p parent = master->active_branch;
	old_master->active_branch = NULL;

	assert(extension->parent->id == 0);
	assert(parent->master == master);
	assert(master->parent == NULL);
	assert(parent);
	assert(parent->arity == 0);
	assert(parent->children == NULL);
	assert(master->open_branches);
	assert(master->open_branches->members != 0);
	assert(extension->selected);
	assert(master->state);
	assert(master->control);
	assert(master->open_branches);
	assert(master->backtracks);
	assert(master->failures);
	assert(parent != parent->master);
	assert(parent->set == parent->open_branches);
	assert(parent->label);
	assert(parent->label->set);

	ClauseTableauApplySubstitution(master, subst);

	TableauSetExtractEntry(parent); // Remove the parent from the collection of open branches
	parent->id = ClauseGetIdent(extension->selected);

	// Register the extension step that we are about to do with stack of backtracks we have available to us.

	Backtrack_p backtrack = BacktrackAlloc(parent, subst, extension->head_lit_position, EXTENSION_RULE);
	PStackPushP(parent->backtracks, backtrack);
	PStack_p position_copy = PStackCopy(backtrack->position);
	PStackPushP(parent->master->master_backtracks, position_copy);

	ClauseSet_p new_leaf_clauses_set = ClauseSetAlloc(); // Copy the clauses of the extension into this

	// This for loop is used for regularity checking.  If the extension would create an irregular branch, block it and return NULL.
	for (Clause_p handle = extension->other_clauses->anchor->succ;
		 handle != extension->other_clauses->anchor;
		 handle = handle->succ)
	{
		Clause_p subst_applied = EtableauClauseCopy(handle, bank, NULL);
		ClauseSetInsert(new_leaf_clauses_set, subst_applied);
		if (ClauseTableauBranchContainsLiteral(parent, subst_applied->literals))
		{
			ClauseSetFree(new_leaf_clauses_set);
			SubstDelete(subst); // If the extension is irregular, delete the substitution and return NULL.
			ClauseTableauFree(master);
			return NULL;  // REGULARITY CHECKING!
		}
		if (extension->head_clause == handle)
		{
			head_literal_clause = subst_applied;
		}
	}

	// At this point, parent has NOT been extended on, so the only way an irregularity can happen is if the OTHER open branches contain one.
	// They have had their labels replaced, and parent is no longer in the open branches set, so we check the remaining open branches.
	if (!ClauseTableauIsLeafRegular(master))
	{
		ClauseSetFree(new_leaf_clauses_set);
		SubstDelete(subst); // If the extension is irregular, delete the substitution and return NULL.
		ClauseTableauFree(master);
		return NULL;  // REGULARITY CHECKING!

	}
	backtrack->completed = true; // The extension is happening at this point.

	long number_of_children = new_leaf_clauses_set->members;

	assert(head_literal_clause);
	assert(number_of_children == extension->other_clauses->members);
	assert(number_of_children > 1);
	assert(head_literal_clause->set == new_leaf_clauses_set);

	parent->children = ClauseTableauArgArrayAlloc(number_of_children);
	Clause_p leaf_clause = NULL;
	// Create children tableau for the leaf labels.  The head literal is labelled as closed.
	for (long p=0; p < number_of_children; p++)
	{
		leaf_clause = ClauseSetExtractFirst(new_leaf_clauses_set);
		parent->children[p] = ClauseTableauChildLabelAlloc(parent, leaf_clause, p);
		assert(leaf_clause);
		assert(parent->children[p]->label);
		assert(parent->children[p]->label->set);
		if (leaf_clause == head_literal_clause)
		{
			parent->children[p]->open = false;
			parent->children[p]->mark_int = 1;
			parent->children[p]->head_lit = true;
		}
		else
		{
			TableauSetInsert(parent->open_branches, parent->children[p]);
			parent->children[p]->open = true;
		}
	}
	assert(ClauseSetEmpty(new_leaf_clauses_set));
	assert(number_of_children == parent->arity);

	ClauseSetFree(new_leaf_clauses_set);
	// Now that the parent has been extended on, it should be removed from the collection of open leaves.
	// Important to do this now, as otherwise folding up or branch saturation may not work correctly.


	// The copying is done, we can delete the subst and print it to the info
	DStrAppendStr(parent->info, " Expansion with clause ");
	DStrAppendInt(parent->info, parent->id);
	DStrAppendStr(parent->info, " ");
	SubstDStrPrint(parent->info, subst, sig, DEREF_NEVER);
	ClauseTableauRegisterStep(parent);

	SubstDelete(subst); // Extremely important.  The backtracks require information from the substitution.

	parent->master->unit_axioms = ClauseSetCopy(bank, old_master->unit_axioms);
	// The work is done- try to close the remaining branches

	FoldUpCloseCycle(parent->master);

	assert(master->master == master);
	PStackPushP(new_tableaux, master);

	// The parent may have been completely closed and extracted
	// from the collection of open branches during the foldup close
	// cycle, or during E saturation proof search on a local branch.

	if (parent->open_branches->members == 0)
	{
		tableaucontrol->closed_tableau = parent->master;
	}

	// There is no need to apply the substitution to the tablaeu, it has already been done by copying labels.
	// In fact, the substitution should be free'd before this function ever returns.
	assert(PStackGetSP(parent->backtracks));
	assert(parent->master == master);
	assert(PStackGetSP(parent->master->master_backtracks));
	return parent->master;
}

/*
** If new_tableaux is passed (to store the new extended tableau) as non-NULL, use the old extension.
** Otherwise use the new version where there is no copy made, and the tableau is directly extended on.
*/
ClauseTableau_p ClauseTableauExtensionRuleWrapper(TableauControl_p tableau_control,
												  TableauExtension_p extension,
												  PStack_p new_tableaux)
{
	if (UNLIKELY(new_tableaux))
	{
		ClauseTableau_p result = ClauseTableauExtensionRuleCopy(tableau_control, new_tableaux, extension);
		return result;
	}
	return ClauseTableauExtensionRuleNoCopy(tableau_control,
											extension);
}

/*
**  Search for contradictions between literals of clauses in extension_candidatees.
**  If an extension is found, return.
**
*/

ClauseTableau_p ClauseTableauSearchForPossibleExtension(TableauControl_p tableaucontrol,
														ClauseTableau_p open_branch,
														ClauseSet_p extension_candidates,
														int *extended,
														TableauStack_p new_tableaux)
{
	Clause_p selected = extension_candidates->anchor->succ;
	ClauseTableau_p closed_tableau = NULL;
	int number_of_extensions = 0;
	assert(ClauseSetCardinality(extension_candidates));

#ifdef LOCAL
	//UpdateLocalVariables(open_branch);
	UpdateLocalVariables2(open_branch);
#else
	assert(open_branch->local_variables == NULL);
#endif

	//while ((selected = select_extension_candidate(extension_candidates)))
	while (selected != extension_candidates->anchor) // iterate over the clauses we can split on the branch
	{
		assert(ClauseLiteralNumber(selected) > 1);
		assert(selected);
		number_of_extensions += ClauseTableauExtensionRuleAttemptOnBranch(tableaucontrol,
																		  open_branch,
																		  NULL,
																		  selected,
																		  new_tableaux);
		if (UNLIKELY(tableaucontrol->closed_tableau))
		{
			closed_tableau = tableaucontrol->closed_tableau;
			break;
		}
		else if (number_of_extensions > 0) // If we extended on the tableau, we have to return and select another branch, unless we are populating
		{
			ETAB_VERBOSE(printf("# Extended on branch at depth %ld\n", open_branch->depth);)
			assert(new_tableaux || number_of_extensions == 1); // Always return after one extension
			*extended += number_of_extensions;
			number_of_extensions = 0;

			// If we are in normal proof search (new_tableaux == NULL) return.
			if (LIKELY(!new_tableaux))
			{
				ClauseSetMoveClause(extension_candidates, selected); // If we just extended with a clause, move it to the end of the extension candidates list.
				break;
			}
		}
		selected = selected->succ;
	}

	return closed_tableau;
}

bool extension_is_strong(ClauseTableau_p parent,
						 ClauseTableau_p grandparent,
						 ClauseSet_p new_leaf_clauses,
						 Clause_p head_literal)
{
	assert(parent);
	assert(grandparent);
	assert(new_leaf_clauses);
	assert(head_literal);
	ProofControl_p proofcontrol = parent->master->control;
	Clause_p leaf_clauses_iterator = new_leaf_clauses->anchor->succ;
	while (leaf_clauses_iterator != new_leaf_clauses->anchor)
	{
		if (leaf_clauses_iterator != head_literal)
		{
			for (long i=0; i<grandparent->arity; i++)
			{
				ClauseTableau_p sister = grandparent->children[i];
				if (sister == parent) continue;
				Clause_p label = sister->label;
				Eqn_p sister_eqn = label->literals;
				Eqn_p leaf_eqn = leaf_clauses_iterator->literals;
				assert(!leaf_eqn->next);
				assert(!sister_eqn->next);
				EqnOrient(proofcontrol->ocb, sister_eqn);
				EqnOrient(proofcontrol->ocb, leaf_eqn);
				if (TermStructEqual(sister_eqn->lterm, leaf_eqn->lterm) &&
				    TermStructEqual(sister_eqn->rterm, leaf_eqn->rterm))
				{
					return false;
				}

			}
		}
		leaf_clauses_iterator = leaf_clauses_iterator->succ;
	}
	return true;
}



// End of file
