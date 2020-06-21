#include "extension.h"
//#include "clausetableaux.h"

TableauExtension_p TableauExtensionAlloc(Clause_p selected,
										 Subst_p subst, 
										 Clause_p head_clause, 
										 ClauseSet_p other_clauses, 
										 ClauseTableau_p parent)
{
	TableauExtension_p handle = TableauExtensionCellAlloc();
	handle->selected = selected;
	handle->subst = subst;
	handle->head_clause = head_clause;
	handle->other_clauses = other_clauses;
	handle->parent = parent;
	handle->succ = NULL;
	return handle;
}

/*  Does not free all objects pointed to.  For use after an extension step has been done.
 * 
*/

void TableauExtensionFree(TableauExtension_p ext)
{
	//SubstDelete(ext->subst);
	//ClauseFree(ext->head_clause);
	//ClauseSetFree(ext->other_clauses);
	TableauExtensionCellFree(ext);
}

ClauseSet_p ClauseStackToClauseSet(ClauseStack_p stack)
{
	PStackPointer number_of_clauses = PStackGetSP(stack);
	ClauseSet_p clauses = ClauseSetAlloc();
	for (PStackPointer i=0; i<number_of_clauses; i++)
	{
		ClauseSetInsert(clauses, PStackElementP(stack, i));
	}
	return clauses;
}

/*-----------------------------------------------------------------------
//
// Function: ClauseSetFreeAnchor()
//
//   Delete a clauseset anchor, removing the clauses from the set but not free'ing them.
//   Warning: May cause memory leaks if you lose track of the clauses!
//
// Global Variables: -
//
// Side Effects    : Memory operations
//
/----------------------------------------------------------------------*/

void ClauseSetFreeAnchor(ClauseSet_p junk)
{
   assert(junk);

   Clause_p handle = NULL;
   
   while ((handle = ClauseSetExtractFirst(junk)))
   {
	   // extract all of the clauses
   }

   if(junk->demod_index)
   {
      PDTreeFree(junk->demod_index);
   }
   if(junk->fvindex)
   {
      FVIAnchorFree(junk->fvindex);
   }
   PDArrayFree(junk->eval_indices);
   ClauseCellFree(junk->anchor);
   DStrFree(junk->identifier);
   ClauseSetCellFree(junk);
}

ClauseSet_p SplitClauseFresh(TB_p bank, ClauseTableau_p tableau, Clause_p clause)
{
	assert(clause);
	ClauseSet_p set = ClauseSetAlloc();
	VarBankSetVCountsToUsed(bank->vars);
	//printf("Clause being copied fresh: ");ClausePrint(GlobalOut, clause, true);printf("\n");
	Clause_p fresh_clause = ClauseCopyFresh(clause, tableau);
	Eqn_p literals = EqnListCopy(fresh_clause->literals, bank);
	Eqn_p lit = NULL;
	Clause_p leaf_clause = NULL;
	short literal_number = ClauseLiteralNumber(fresh_clause);
	for (short i=0; i < literal_number; i++)
	{
		lit = EqnListExtractFirst(&literals);
		leaf_clause = ClauseAlloc(lit);
		ClauseSetInsert(set, leaf_clause);
	}
	EqnListFree(literals);
	ClauseFree(fresh_clause);
	assert(set->members == literal_number);
	return set;
}

// Check to see if the literals of clause occur in the branch already.

bool ClauseTableauExtensionIsRegular(ClauseTableau_p branch, Clause_p clause)
{
	for (Eqn_p lit = clause->literals; lit; lit = lit->next)
	{
		if (ClauseTableauBranchContainsLiteral(branch, lit))
		{
			//printf("Irregular extension: ");ClausePrint(GlobalOut, clause, true);printf("\n");
			//ClauseTableauPrintBranch(branch);
			return false;
		}
	}
	return true;
}


/*  Actually does an extension rule application.  head_literal_location is the PStackPointer corresponding of the head clause in 
 * 	new_leaf_clauses.  literal_number is the number of literals in the clause that is being split in the extension rule application.
 *  This method is only called by ClauseTableauExtensionRuleAttempt.  If this method is called there is likely a Subst_p active!
 * 
 *  Does not modify the old tableau!  A copy of it is made, which is then extended.
f *  This is because we may need the old unmodified tableau for other extension steps,
 *  or undo the work if the extension is irregular.  Irregular extensions are 
 *  detected after the work is done.
*/

ClauseTableau_p ClauseTableauExtensionRule(TableauControl_p tableau_control,
														 TableauSet_p distinct_tableaux, 
														 TableauExtension_p extension, 
														 PStack_p new_tableaux)
{
	// Create a copy of the master tableau of the extension rule's tableau.
	// Insert the newly created master tableau in to the distinct_tableaux. 
	ClauseTableau_p old_tableau_master = extension->parent->master;
	old_tableau_master->active_branch = extension->parent;
	ClauseTableau_p tableau_copy = ClauseTableauMasterCopy(old_tableau_master);  //there may be a subst active
	
	assert(extension->parent->id == 0);
	assert(old_tableau_master->parent == NULL);
	assert(distinct_tableaux);
	assert(tableau_copy->open_branches);
	assert(tableau_copy->open_branches->members != 0);
	assert(tableau_copy->active_branch);
	assert(tableau_copy->master == tableau_copy);
	assert(extension->selected);
	
	// Do the extension rule on the active branch of the newly created tableau
	
	ClauseTableau_p parent = tableau_copy->active_branch;
	tableau_copy->active_branch = NULL; // We have the handle where we are working, so set this to NULL to indicate this.
	
	parent->id = ClauseGetIdent(extension->selected);
	
	Clause_p head_literal_clause = NULL;
	TB_p bank = parent->terms;
	Sig_p sig = bank->sig;
	bool regular = true;
	ClauseSet_p new_leaf_clauses_set = ClauseSetAlloc(); // Copy the clauses of the extension
	for (Clause_p handle = extension->other_clauses->anchor->succ;
					  handle != extension->other_clauses->anchor;
					  handle = handle->succ)
	{
		Clause_p subst_applied = ClauseCopy(handle, bank);
		ClauseSetInsert(new_leaf_clauses_set, subst_applied);
		if (extension->head_clause == handle)
		{
			head_literal_clause = subst_applied;
		}
	}
	long number_of_children = new_leaf_clauses_set->members;
	
	assert(head_literal_clause);
	assert(number_of_children == extension->other_clauses->members);
	assert(head_literal_clause->set == new_leaf_clauses_set);
	
	parent->children = ClauseTableauArgArrayAlloc(number_of_children);
	Clause_p leaf_clause = NULL;
	// Create children tableau for the leaf labels.  The head literal is labelled as closed.
	for (long p=0; p < number_of_children; p++)
	{
		leaf_clause = ClauseSetExtractFirst(new_leaf_clauses_set);
		if (regular && ClauseTableauBranchContainsLiteral(parent, leaf_clause->literals))
		{
			regular = false;  // REGULARITY CHECKING!
		}
		assert(leaf_clause);
		parent->children[p] = ClauseTableauChildLabelAlloc(parent, leaf_clause, p);
		if (leaf_clause == head_literal_clause)
		{
			parent->children[p]->open = false; 
			parent->children[p]->mark_int = 1;
			parent->children[p]->head_lit = true;
			SubstDStrPrint(parent->children[p]->info, extension->subst, sig, DEREF_ONCE); 
		}
		else
		{
			TableauSetInsert(parent->open_branches, parent->children[p]);
			parent->children[p]->open = true;
		}
	}
	
	// Now that the parent has been extended on, it should be removed from the collection of open leaves.
	// Important to do this now, as otherwise folding up or branch saturation may not work correctly.
	
	if (parent->set)
	{
		TableauSetExtractEntry(parent);
	}
	
	//  If this tableau is irregular, we have to undo all of the work.
	//  This can probably be detected earlier to save
	//  unnecessary allocations and work.
	if (!regular)
	{
		assert(new_leaf_clauses_set->members == 0);
		ClauseSetFree(new_leaf_clauses_set);
		ClauseTableauFree(parent->master);
		//SubstDelete(extension->subst);
		return NULL;
	}
	else // the extension is regular- add it to the new tabeleax to be processed later
	{
		PStackPushP(new_tableaux, parent->master);
	}
	
	// The work is done- try to close the remaining branches
	//SubstDelete(extension->subst);
	
	FoldUpCloseCycle(parent->master);
	
	// The parent may have been completely closed and extracted
	// from the collection of open branches during the foldup close
	// cycle.
	
	if (parent->open_branches->members == 0)
	{
		//printf("# Closed tableau found.\n");
		//ClauseTableauPrintDOTGraph(parent->master);
		tableau_control->closed_tableau = parent->master;
		ClauseSetFree(new_leaf_clauses_set);
		return parent;
	}
	
	// We have tried to close the remaining branches with closure rule- try superposition
	// on the remaining local branches.
	assert(parent->master->state);
	assert(parent->master->control);
	ProofState_p proofstate = parent->master->state;
	ProofControl_p proofcontrol = parent->master->control;
	
	if ((parent->open_branches->anchor->succ->depth % 3) == 0)
	{
		BranchSaturation_p branch_saturation = BranchSaturationAlloc(proofstate, proofcontrol, parent->master);
		// Trying to keep one object in extensions and saturations
		AttemptToCloseBranchesWithSuperposition(tableau_control, branch_saturation);
		BranchSaturationFree(branch_saturation);
	}
	fflush(GlobalOut);
	
	// The parent may have been completely closed and extracted
	// from the collection of open branches during the foldup close
	// cycle.
	
	assert(number_of_children == parent->arity);
	assert(parent->arity == number_of_children);
	assert(new_leaf_clauses_set->members == 0);
	
	// There is no need to apply the substitution to the tablaeu, it has already been done by copying labels.
	ClauseSetFree(new_leaf_clauses_set);
	return parent;
}

/*  Do all of the extension rules possible with the selected clause.
 *  There may be multiple literals extension can be done with.
 *  The resulting tableaux are added to distinct_tableaux.
 *  At the end, when all of the new tableaux are created, the original tableau is removed from
 *  distinct_tableaux.
*/

int ClauseTableauExtensionRuleAttemptOnBranch(TableauControl_p tableau_control,
															 ClauseTableau_p open_branch, 
															 TableauSet_p distinct_tableaux,
															 Clause_p selected,
															 PStack_p new_tableaux)
{
	int extensions_done = 0;
	int subst_completed = 0;
	ClauseSet_p new_leaf_clauses = SplitClauseFresh(open_branch->terms, open_branch->master, selected);
	assert(new_leaf_clauses->members);
	Subst_p subst = SubstAlloc();
	Subst_p success_subst = NULL;
	PStackPointer local_subst_length = 0;
	Clause_p leaf_clause = new_leaf_clauses->anchor->succ;
	
	Clause_p open_branch_label = open_branch->label;
	long num_local_variables = UpdateLocalVariables(open_branch);
	if (num_local_variables)
	{
		assert(PStackGetSP(open_branch->local_variables) > 0);
		open_branch_label = ReplaceLocalVariablesWithFreshSubst(open_branch->master,
																			open_branch_label,
																			open_branch->local_variables,
																			subst);
		local_subst_length = PStackGetSP(subst);
	}
	while (leaf_clause != new_leaf_clauses->anchor)
	{
		assert(open_branch);
		assert(open_branch != open_branch->open_branches->anchor);
		assert(open_branch->parent);
		assert(open_branch->label);
		assert(open_branch->arity == 0);
		assert(leaf_clause);
		assert(selected);
		PStackPointer extension_contradiction_length = 0;
		
		// Here we are only doing the first possible extension- need to create a list of all of the extensions and do them...
		// The subst, leaf_clause, new_leaf_clauses, will have to be reset, but the open_branch can remain the same since we have not affected it.
		if ((success_subst = ClauseContradictsClauseSubst(leaf_clause, open_branch_label, subst))) // stricter extension step
		{
			subst_completed++;
			//~ printf("=== %ld\n", ClauseGetIdent(selected));
			//~ SubstPrint(GlobalOut,subst, open_branch->master->terms->sig, DEREF_NEVER);printf("\n");
			//~ ClausePrint(GlobalOut, leaf_clause, true);printf("\n");
			//~ ClausePrint(GlobalOut, open_branch_label, true);printf("\n");
			//~ printf("===\n");
			Clause_p head_clause = leaf_clause;
			TableauExtension_p extension_candidate = TableauExtensionAlloc(selected, 
																		   subst, 
																		   head_clause, 
																		   new_leaf_clauses, 
																		   open_branch);
			ClauseTableau_p maybe_extended = ClauseTableauExtensionRule(tableau_control,
																							distinct_tableaux, 
																							extension_candidate, 
																							new_tableaux);
			TableauExtensionFree(extension_candidate);
			if (maybe_extended) // extension may not happen due to regularity
			{
				//printf("# Extension completed.  There are %ld new_tableaux\n", PStackGetSP(new_tableaux));
				extensions_done++;
				if (maybe_extended->open_branches->members == 0)
				{
					fprintf(GlobalOut, "# Closed tableau found!\n");
					assert(maybe_extended->master->label);
					tableau_control->closed_tableau = maybe_extended->master;
					ClauseSetFree(new_leaf_clauses);
					SubstDelete(subst);
					return extensions_done;
				}
			}
			SubstBacktrackToPos(subst, local_subst_length);
		}
		leaf_clause = leaf_clause->succ;
	}
	if (num_local_variables)
	{
		ClauseFree(open_branch_label);
	}
	
	// Do not work here.  The tableau of open branch has been copied and worked on. 
	// The current open branch is now "old" and will only be used for other extensions.
   
   //  OK We're done
   SubstDelete(subst);
   ClauseSetFree(new_leaf_clauses);
	return extensions_done;
}
