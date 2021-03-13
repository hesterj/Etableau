#include "etab_extension.h"
//#include "clausetableaux.h"

TableauExtension_p TableauExtensionAlloc(Clause_p selected,
										 Subst_p subst, 
										 Clause_p head_clause, 
										 ClauseSet_p other_clauses, 
										 ClauseTableau_p parent,
										 short head_lit_position)
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
		Clause_p clause = PStackElementP(stack, i);
		if (clause->set)
		{
			ClauseSetExtractEntry(clause);
		}
		ClauseSetInsert(clauses, clause);
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
   //DStrFree(junk->identifier);
   ClauseSetCellFree(junk);
}

ClauseSet_p SplitClauseFresh(TB_p bank, ClauseTableau_p tableau, Clause_p clause)
{
	assert(clause);
	assert(tableau);
	ClauseSet_p set = ClauseSetAlloc();
	//VarBankSetVCountsToUsed(bank->vars);
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
	TB_p bank = extension->parent->terms;
	Clause_p head_literal_clause = NULL;
	ClauseSet_p new_leaf_clauses_set = ClauseSetAlloc(); // Copy the clauses of the extension
	Subst_p subst = extension->subst;
	// failure caching check here?
	for (Clause_p handle = extension->other_clauses->anchor->succ;
					  handle != extension->other_clauses->anchor;
					  handle = handle->succ)
	{
		if (ClauseTableauBranchContainsLiteral(extension->parent, handle->literals))
		{
			ClauseSetFree(new_leaf_clauses_set);
			SubstDelete(subst); // If the extension is irregular, delete the substitution and return NULL.
			return NULL;  // REGULARITY CHECKING!
		}
		Clause_p subst_applied = ClauseCopy(handle, bank);
		ClauseSetInsert(new_leaf_clauses_set, subst_applied);
		if (extension->head_clause == handle)
		{
			head_literal_clause = subst_applied;
		}
	}
	long number_of_children = new_leaf_clauses_set->members;
	// Create a copy of the master tableau of the extension rule's tableau.
	// Insert the newly created master tableau in to the distinct_tableaux. 
	ClauseTableau_p old_tableau_master = extension->parent->master;
	old_tableau_master->active_branch = extension->parent;
	ClauseTableau_p tableau_copy = ClauseTableauMasterCopy(old_tableau_master);  //there may be a subst active
	Sig_p sig = tableau_copy->terms->sig;
	assert(extension->parent->id == 0);
	assert(old_tableau_master->parent == NULL);
	assert(tableau_copy->open_branches);
	assert(tableau_copy->open_branches->members != 0);
	assert(tableau_copy->active_branch);
	assert(tableau_copy->master == tableau_copy);
	assert(extension->selected);
	// Do the extension rule on the active branch of the newly created tableau
	
	ClauseTableau_p parent = tableau_copy->active_branch;
	tableau_copy->active_branch = NULL; // We have the handle where we are working, so set this to NULL to indicate this.
	
	parent->id = ClauseGetIdent(extension->selected);
	
	
	assert(head_literal_clause);
	assert(number_of_children == extension->other_clauses->members);
	assert(head_literal_clause->set == new_leaf_clauses_set);
	
	parent->children = ClauseTableauArgArrayAlloc(number_of_children);
	Clause_p leaf_clause = NULL;
	// Create children tableau for the leaf labels.  The head literal is labelled as closed.
	for (long p=0; p < number_of_children; p++)
	{
		leaf_clause = ClauseSetExtractFirst(new_leaf_clauses_set);
		//if (regular && ClauseTableauBranchContainsLiteral(parent, leaf_clause->literals))
		//{
			//regular = false;  // REGULARITY CHECKING!
		//}
		assert(leaf_clause);
		parent->children[p] = ClauseTableauChildLabelAlloc(parent, leaf_clause, p);
		assert(parent->children[p]->label);
		assert(parent->children[p]->label->set);
		if (leaf_clause == head_literal_clause)
		{
			parent->children[p]->open = false; 
			parent->children[p]->mark_int = 1;
			parent->children[p]->head_lit = true;
			//SubstDStrPrint(parent->children[p]->info, extension->subst, sig, DEREF_ONCE); 
		}
		else
		{
			TableauSetInsert(parent->open_branches, parent->children[p]);
			parent->children[p]->open = true;
		}
	}
	
	// Now that the parent has been extended on, it should be removed from the collection of open leaves.
	// Important to do this now, as otherwise folding up or branch saturation may not work correctly.
	
	assert(parent != parent->master);
	if (parent->set == parent->open_branches)
	{
		TableauSetExtractEntry(parent);
	}
	assert(parent->master);
	PStackPushP(new_tableaux, parent->master);

	// The copying is done, we can delete the subst and print it to the info
	DStrAppendStr(parent->info, " Expansion with clause ");
	DStrAppendInt(parent->info, parent->id);
	DStrAppendStr(parent->info, " ");
	SubstDStrPrint(parent->info, subst, sig, DEREF_NEVER);
	ClauseTableauRegisterStep(parent);
	SubstDelete(subst); // Extremely important!

	// Protect the unit axioms from the dirty substitution by copying them now...
	parent->master->unit_axioms = ClauseSetCopy(parent->master->terms, old_tableau_master->unit_axioms);
	
	// The work is done- try to close the remaining branches
	
	FoldUpCloseCycle(parent->master);
	
	
	// The parent may have been completely closed and extracted
	// from the collection of open branches during the foldup close
	// cycle, or during E saturation proof search on a local branch.
	
	if (parent->open_branches->members == 0)
	{
		//printf("# Closed tableau found.\n");
		//ClauseTableauPrintDOTGraph(parent->master);
		tableau_control->closed_tableau = parent->master;
		ClauseSetFree(new_leaf_clauses_set);
		return parent->master;
	}
	
	assert(parent->master->state);
	assert(parent->master->control);
	assert(number_of_children == parent->arity);
	assert(parent->arity == number_of_children);
	assert(new_leaf_clauses_set->members == 0);
	assert(parent->master->open_branches);
	assert(parent->master->label);
	
	// There is no need to apply the substitution to the tablaeu, it has already been done by copying labels.
	// In fact, the substitution should be free'd before this function ever returns.
	ClauseSetFree(new_leaf_clauses_set);
	return parent->master;
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
											  TableauStack_p new_tableaux)
{
	int extensions_done = 0;
	int subst_completed = 0;
	//long split_clause_ident = ClauseGetIdent(selected);
	//if (split_clause_ident == open_branch->parent->id) return 0; // Don't split the same clause twice
	
	//  SplitClauseFresh here is a major performance offender.
	ClauseTableauUpdateVariables(open_branch->master);
	ClauseSet_p new_leaf_clauses = SplitClauseFresh(open_branch->terms, open_branch->master, selected);
	assert(new_leaf_clauses->members);
	Clause_p open_branch_label = open_branch->label;

#ifdef LOCAL
	long num_local_variables = UpdateLocalVariables(open_branch);
	if (num_local_variables)
	{
		assert(PStackGetSP(open_branch->local_variables) > 0);
		open_branch_label = ReplaceLocalVariablesWithFresh(open_branch->master,
														   open_branch_label,
														   open_branch->local_variables);
		//ClauseSet_p label_storage = tableau_control->label_storage;
		ClauseSetExtractEntry(open_branch->label);
		ClauseFree(open_branch->label);
		open_branch->label = open_branch_label;
		assert(open_branch->label->set);
		//ClauseSetInsert(label_storage, open_branch_label);
	}
#endif
	
	Clause_p leaf_clause = new_leaf_clauses->anchor->succ;
	short position = 0; // This is the position of the current leaf clause in the split clause
	while (leaf_clause != new_leaf_clauses->anchor)
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
		assert(selected);
		Subst_p subst = SubstAlloc();
		Subst_p success_subst = NULL;
		
		//fprintf(GlobalOut, "Clause A (%ld): ", split_clause_ident);ClausePrint(GlobalOut, leaf_clause, true);printf("\n");
		//fprintf(GlobalOut, "Clause B (branch): ");ClausePrint(GlobalOut, open_branch_label, true);printf("\n");
		
		// Here we are only doing the first possible extension- need to create a list of all of the extensions and do them...
		// The subst, leaf_clause, new_leaf_clauses, will have to be reset, but the open_branch can remain the same since we have not affected it.
		if ((success_subst = ClauseContradictsClauseSubst(leaf_clause, open_branch_label, subst))) // stricter extension step
		{
			subst_completed++;
			assert(open_branch->master->label);
			Clause_p head_clause = leaf_clause;
			TableauExtension_p extension_candidate = TableauExtensionAlloc(selected,
																		   success_subst, 
																		   head_clause, 
																		   new_leaf_clauses, 
																		   open_branch,
																		   position);
			// If there is no new_tableaux stack passed to the function we are in, the extension is done on the tableau itself
			ClauseTableau_p extended = ClauseTableauExtensionRuleWrapper(tableau_control,
																		 extension_candidate,
																		 new_tableaux);
			TableauExtensionFree(extension_candidate);
			if (extended) // extension may not happen due to regularity
			{
				extensions_done++;
				//fprintf(stdout, "#");
				tableau_control->number_of_extensions++;
				if (tableau_control->branch_saturation_enabled)
				{
					//fprintf(GlobalOut, "# Saturating branch\n");
					BranchSaturation_p branch_sat = BranchSaturationAlloc(tableau_control->proofstate, 
																		  tableau_control->proofcontrol,
																		  extended->master,
																		  10000);
					AttemptToCloseBranchesWithSuperpositionSerial(tableau_control, branch_sat);
					BranchSaturationFree(branch_sat);
					//fprintf(GlobalOut, "# Saturation done\n");
				}
				if (LIKELY(!new_tableaux) || PStackGetSP(new_tableaux) >= tableau_control->multiprocessing_active) // If we extended on a tableau without copying it, return.
				{
					goto return_point;
				}
			}
		}
		else
		{
			// If an extension is attempted, the substitution is free'd in that method
			// Otherwise, we must free it here
			SubstDelete(subst);
		}
		//fprintf(GlobalOut, "# Next leaf clause...\n");
		position++;
		leaf_clause = leaf_clause->succ;
	}

	// Do not work here.  The tableau of open branch has been copied and worked on.
	// The current open branch is now "old" and will only be used for other extensions.
   
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

	//if (SubstIsFailure(extension->parent, subst))
	//{
		//fprintf(GlobalOut, "# Failure substitution!\n");
		//SubstDelete(subst);
		//return NULL;
	//}
	if (ExtensionIsFailure(extension->parent, subst, ClauseGetIdent(extension->selected), extension->head_lit_position))
	{
		//fprintf(GlobalOut, "# Failure substitution in extension!\n");
		SubstDelete(subst);
		return NULL;
	}

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
		Clause_p subst_applied = ClauseCopy(handle, bank);
		ClauseSetInsert(new_leaf_clauses_set, subst_applied);
		//if (ClauseTableauBranchContainsLiteral(parent, handle->literals))
		if (ClauseTableauBranchContainsLiteral(parent, subst_applied->literals))
		{
			//fprintf(GlobalOut, "# Irregular extension stopped at parent\n");
			ClauseSetFree(new_leaf_clauses_set);
			SubstDelete(subst); // If the extension is irregular, delete the substitution and return NULL.
			__attribute__((unused)) bool backtracked = BacktrackWrapper(master, false);
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
		//fprintf(GlobalOut, "# Irregular extension stopped at non-parent\n");
		ClauseSetFree(new_leaf_clauses_set);
		SubstDelete(subst); // If the extension is irregular, delete the substitution and return NULL.
		__attribute__((unused)) bool backtracked = BacktrackWrapper(master, false);
		assert(backtracked);
		return NULL;  // REGULARITY CHECKING!

	}
	backtrack->completed = true; // The extension is happening at this point.

	short number_of_children = (short) new_leaf_clauses_set->members;

	assert(head_literal_clause);
	assert(number_of_children == extension->other_clauses->members);
	assert(number_of_children > 1);
	assert(head_literal_clause->set == new_leaf_clauses_set);

	parent->children = ClauseTableauArgArrayAlloc(number_of_children);
	Clause_p leaf_clause = NULL;
	// Create children tableau for the leaf labels.  The head literal is labelled as closed.
	for (short p=0; p < number_of_children; p++)
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
	Subst_p subst = extension->subst;
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

	/*
	**  If this extension has already been performed at this node and failed, it must be prevented.
	*/

	if (ExtensionIsFailure(extension->parent, subst, ClauseGetIdent(extension->selected), extension->head_lit_position))
	{
		//fprintf(GlobalOut, "# Failure substitution in extension!\n");
		SubstDelete(subst);
		ClauseTableauFree(master);
		return NULL;
	}

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
		Clause_p subst_applied = ClauseCopy(handle, bank);
		ClauseSetInsert(new_leaf_clauses_set, subst_applied);
		//if (ClauseTableauBranchContainsLiteral(parent, handle->literals))
		if (ClauseTableauBranchContainsLiteral(parent, subst_applied->literals))
		{
			//fprintf(GlobalOut, "# Irregular extension stopped at parent\n");
			ClauseSetFree(new_leaf_clauses_set);
			SubstDelete(subst); // If the extension is irregular, delete the substitution and return NULL.
			__attribute__((unused)) bool backtracked = BacktrackWrapper(master, false);
			assert(backtracked);
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
		//fprintf(GlobalOut, "# Irregular extension stopped at non-parent\n");
		ClauseSetFree(new_leaf_clauses_set);
		SubstDelete(subst); // If the extension is irregular, delete the substitution and return NULL.
		__attribute__((unused)) bool backtracked = BacktrackWrapper(master, false);
		assert(backtracked);
		ClauseTableauFree(master);
		return NULL;  // REGULARITY CHECKING!

	}
	backtrack->completed = true; // The extension is happening at this point.

	short number_of_children = (short) new_leaf_clauses_set->members;

	assert(head_literal_clause);
	assert(number_of_children == extension->other_clauses->members);
	assert(number_of_children > 1);
	assert(head_literal_clause->set == new_leaf_clauses_set);

	parent->children = ClauseTableauArgArrayAlloc(number_of_children);
	Clause_p leaf_clause = NULL;
	// Create children tableau for the leaf labels.  The head literal is labelled as closed.
	for (short p=0; p < number_of_children; p++)
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
														int max_depth,
														int *extended,
														TableauStack_p new_tableaux)
{
    Clause_p selected = extension_candidates->anchor->succ;
	ClauseTableau_p closed_tableau = NULL;
    int number_of_extensions = 0;
    while (selected != extension_candidates->anchor) // iterate over the clauses we can split on the branch
    {
        //fprintf(GlobalOut, "# Attempting to expand with clause...\n");
        number_of_extensions += ClauseTableauExtensionRuleAttemptOnBranch(tableaucontrol,
                                                                          open_branch,
                                                                          NULL,
                                                                          selected,
                                                                          new_tableaux);
        if (UNLIKELY(tableaucontrol->closed_tableau))
        {
            closed_tableau = tableaucontrol->closed_tableau;
            //fprintf(GlobalOut, "# Success\n");
            break;
        }
        else if (number_of_extensions > 0)
        {
            assert(new_tableaux || number_of_extensions == 1); // Always return after one extension
			*extended += number_of_extensions;
            //fprintf(GlobalOut, "#  Extended on a branch at depth %d...\n", open_branch->depth);
            if (LIKELY(!new_tableaux) || PStackGetSP(new_tableaux) >= tableaucontrol->multiprocessing_active)
			{
				break;
			}
        }
        selected = selected->succ;
    }
	return closed_tableau;
}
