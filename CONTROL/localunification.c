#include <localunification.h>

/*  This method updates the local variables of the node.
 * This is intended to be used on the leaf node of a branch.
 * Variables that are local (do not occur on any open branch but
 * this one) can be treated with the local extension rule and local
 * reduction rule.
 * 
 *   It first iterates up the branch of the node, collecting
 * all variables of the branch.  Then it iterates up the other 
 * open branches of the tableau, removing any variables that occur 
 * in the other branches.
 * 
 *   The method returns the number of local variables for node's 
 * branch.  The local variables stack of node is deleted if it
 * exists.
*/

long UpdateLocalVariables(ClauseTableau_p node)
{
	long num_variables = 0;
	PTree_p local_variables_tree = NULL;
	if (node->local_variables)
	{
		PStackFree(node->local_variables);
	}
	PStack_p local_variables = PStackAlloc();
	// Collect the variables in the current branch
	
	num_variables += CollectVariablesOfBranch(node, &local_variables_tree, true);
	
	// Collect the variables of the other branches
	ClauseTableau_p branch_iterator = node->open_branches->anchor->succ;
	PTree_p temp_variable_tree = NULL;
	while (branch_iterator != node->open_branches->anchor)
	{
		if (branch_iterator != node)
		{
			CollectVariablesOfBranch(branch_iterator, &temp_variable_tree, false);
		}
		branch_iterator = branch_iterator->succ;
	}
	PStack_p other_branches_vars_stack = PStackAlloc();
	PTreeToPStack(other_branches_vars_stack, temp_variable_tree);
	
	// If a variable occurs in another branch, remove it from the tree of local variables
	while (!PStackEmpty(other_branches_vars_stack))
	{
		Term_p other_branch_variable = PStackPopP(other_branches_vars_stack);
		PTreeDeleteEntry(&local_variables_tree, other_branch_variable);
	}
	num_variables = PTreeToPStack(local_variables, local_variables_tree);
	node->local_variables = local_variables;
	
#ifndef DNDEBUG
	if (num_variables)
	{
		//printf("%ld Local variables found! ", num_variables);
		for (PStackPointer p = 0; p<PStackGetSP(local_variables); p++)
		{
			Term_p local_variable = PStackElementP(local_variables, p);
			//printf("# Local variable ");
			//TermPrint(GlobalOut, local_variable, sig,DEREF_ALWAYS);
			//TermPrint(GlobalOut, local_variable, node->terms->sig, DEREF_ALWAYS);printf(" ");
			if (PTreeFind(&temp_variable_tree, local_variable))
			{
				printf("Found local variable in other branches var tree...\n");
				printf("Root of temp_variable_tree: %7p\n", temp_variable_tree->key);
				printf("Able to delete? %d\n", PTreeDeleteEntry(&temp_variable_tree, local_variable));
				printf("Root of temp_variable_tree: %7p\n", temp_variable_tree->key);
				printf("%ld nodes in temp_variable_tree.\n", PTreeNodes(temp_variable_tree));
				//TermPrint(GlobalOut, temp_variable_tree->key, node->terms->sig, DEREF_ALWAYS);printf("\n");
				Error("Found local variable in another branch...", 1);
			}
			
		}
	}
#endif

	PStackFree(other_branches_vars_stack);
	PTreeFree(temp_variable_tree);
	PTreeFree(local_variables_tree);
	return num_variables;
}

/*  Returns number of variables found
 * 
*/

long CollectVariablesOfBranch(ClauseTableau_p branch, PTree_p *branch_vars, bool include_root)
{
	long num_variables = 0;
	ClauseTableau_p iterator = branch;
	while (iterator)
	{
		if ((iterator != branch->master) || (include_root))
		{
			num_variables += CollectVariablesAtNode(iterator, branch_vars);
		}
		iterator = iterator->parent;
	}
	return num_variables;
}

/*  At a node in a tableau, there are folding_labels, the label itself, and 
 * unit axioms at the root node.  This method collects all the variables of the aforementioned in to stack.  The number of
 * variables found is returned.
*/

long CollectVariablesAtNode(ClauseTableau_p node, PTree_p *var_tree)
{
   long num_collected = 0;
   
   num_collected += ClauseCollectVariables(node->label, var_tree);
	
   Clause_p handle;
   if (node->folding_labels)
   {
	   for(handle = node->folding_labels->anchor->succ; handle!= node->folding_labels->anchor; handle =
			  handle->succ)
	   {
		  num_collected += ClauseCollectVariables(handle, var_tree);
	   }
   }
	
	return num_collected;
}

/*  Only call this method if the local variables of the tableau have been udpated!
 *  This method incorporates the replacement of replacements of variables with fresh ones into subst.
*/

Clause_p ReplaceLocalVariablesWithFreshSubst(ClauseTableau_p master, Clause_p clause, PStack_p local_variables, Subst_p subst)
{
	Clause_p new_clause = NULL;
	assert(PStackGetSP(local_variables));
	//printf("Old clause: ");ClausePrint(GlobalOut, clause, true);printf("\n");
	//Subst_p subst = SubstAlloc();
	for (PStackPointer p = 0; p < PStackGetSP(local_variables); p++)
	{
		Term_p old_var = PStackElementP(local_variables, p);
		assert(old_var);
		assert(old_var->f_code < 0);
		master->max_var -= 2;
		//Term_p fresh_var = VarBankVarAssertAlloc(variable_bank, master->max_var, old_var->type);
		Term_p fresh_var = VarBankGetFreshVar(master->state->freshvars, old_var->type);
		assert(old_var != fresh_var);
		assert(old_var->f_code != fresh_var->f_code);
		SubstAddBinding(subst, old_var, fresh_var);
	}
	new_clause = ClauseCopy(clause, master->terms);
	//printf("New clause with binding: ");ClausePrint(GlobalOut, new_clause, true);printf("\n");
	//SubstDelete(subst);
	return new_clause;
}

/*  Only call this method if the local variables of the tableau have been udpated!
 *  This method deletes the substitution used in the replacement.
*/

Clause_p ReplaceLocalVariablesWithFresh(ClauseTableau_p master, Clause_p clause, PStack_p local_variables)
{
	Clause_p new_clause = NULL;
	assert(PStackGetSP(local_variables));
	VarBank_p variable_bank = master->terms->vars;
	//printf("Old clause: ");ClausePrint(GlobalOut, clause, true);printf("\n");
	Subst_p subst = SubstAlloc();
	for (PStackPointer p = 0; p < PStackGetSP(local_variables); p++)
	{
		Term_p old_var = PStackElementP(local_variables, p);
		assert(old_var);
		assert(old_var->f_code < 0);
		master->max_var -= 2;
		//Term_p fresh_var = VarBankVarAssertAlloc(variable_bank, master->max_var, old_var->type);
		//VarBankSetVCountsToUsed(variable_bank);
		Term_p fresh_var = VarBankGetFreshVar(variable_bank, old_var->type);
		assert(fresh_var != old_var);
		//~ Term_p fresh_var = old_var;
		//~ while (old_var == fresh_var)
		//~ {
			//~ master->max_var -= 2;
			//~ fresh_var = VarBankVarAssertAlloc(variable_bank, master->max_var, old_var->type);
		//~ }
		assert(old_var->f_code != fresh_var->f_code);
		SubstAddBinding(subst, old_var, fresh_var);
	}
	new_clause = ClauseCopyOpt(clause);
	//printf("New clause with binding: ");ClausePrint(GlobalOut, new_clause, true);printf("\n");
	SubstDelete(subst);
	return new_clause;
}

/*  Return true if the branch is local
 *  Side Effect: Updates local variables of branch
*/

bool BranchIsLocal(ClauseTableau_p branch)
{
	PTree_p branch_vars = NULL;
	long local_vars = UpdateLocalVariables(branch);
	long num_vars = CollectVariablesOfBranch(branch, &branch_vars, true);
#ifndef DNDEBUG
	long branch_local_variables = PStackGetSP(branch->local_variables);
	assert(branch_local_variables == local_vars);
#endif
	//printf("# %ld local vars, %ld total vars\n", local_vars, num_vars);
	if (num_vars == 0)
	{
		PTree_p temp = NULL;
		ClauseCollectVariables(branch->label, &temp);
		PTreeFree(temp);
	}
	if (local_vars == num_vars)
	{
		//printf("# Local branch\n");
		//PTreeDebugPrint(GlobalOut, branch_vars);
		return true;
	}
	PTreeFree(branch_vars);
	return false;
	
}

bool AllBranchesAreLocal(ClauseTableau_p master)
{
	ClauseTableau_p branch_handle = master->open_branches->anchor->succ;
	while (branch_handle != master->open_branches->anchor)
	{
		bool local = BranchIsLocal(branch_handle);
		if (!local)
		{
			return false;
		}
		branch_handle = branch_handle->succ;
	}
	printf("# All branches are local!\n");
	return true;
}
