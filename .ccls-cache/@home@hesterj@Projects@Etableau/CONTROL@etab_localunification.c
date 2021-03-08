#include <etab_localunification.h>

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
			//CollectVariablesOfBranch(branch_iterator, &temp_variable_tree, false);
			CollectVariablesOfBranch(branch_iterator, &temp_variable_tree, true); // We need to include the root, otherwise branches could share variables there...
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
	
	//if (num_variables)
	//{
		//printf("%ld Local variables found! ", num_variables);
		//for (PStackPointer p = 0; p<PStackGetSP(local_variables); p++)
		//{
			//Term_p local_variable = PStackElementP(local_variables, p);
			////printf("# Local variable ");
			////TermPrint(GlobalOut, local_variable, sig,DEREF_ALWAYS);
			////TermPrint(GlobalOut, local_variable, node->terms->sig, DEREF_ALWAYS);printf(" ");
			//if (PTreeFind(&temp_variable_tree, local_variable))
			//{
				//printf("Found local variable in other branches var tree...\n");
				//printf("Root of temp_variable_tree: %7p\n", temp_variable_tree->key);
				//printf("Able to delete? %d\n", PTreeDeleteEntry(&temp_variable_tree, local_variable));
				//printf("Root of temp_variable_tree: %7p\n", temp_variable_tree->key);
				//printf("%ld nodes in temp_variable_tree.\n", PTreeNodes(temp_variable_tree));
				////TermPrint(GlobalOut, temp_variable_tree->key, node->terms->sig, DEREF_ALWAYS);printf("\n");
				//Error("Found local variable in another branch...", 1);
			//}
		//
		//}
	//}

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
   assert(node);
   assert(node->label);
   
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

long ClauseCollectVariablesStack(Clause_p clause, PStack_p stack)
{
	assert(false);
	return 0;
}

/*  Only call this method if the local variables of the tableau have been udpated!
 *  This method incorporates the replacement of replacements of variables with fresh ones into subst.
*/

Clause_p ReplaceLocalVariablesWithFreshSubst(ClauseTableau_p master, Clause_p clause, PStack_p local_variables, Subst_p subst)
{
	Clause_p new_clause = NULL;
	assert(PStackGetSP(local_variables));
	for (PStackPointer p = 0; p < PStackGetSP(local_variables); p++)
	{
		Term_p old_var = PStackElementP(local_variables, p);
		assert(old_var);
		assert(old_var->f_code < 0);
		Term_p fresh_var = ClauseTableauGetFreshVar(master->master, old_var);
		assert(old_var != fresh_var);
		assert(old_var->f_code != fresh_var->f_code);
		SubstAddBinding(subst, old_var, fresh_var);
	}
	new_clause = ClauseCopy(clause, master->terms);
	return new_clause;
}

/*  Only call this method if the local variables of the tableau have been udpated!
 *  This method deletes the substitution used in the replacement.
*/

Clause_p ReplaceLocalVariablesWithFresh(ClauseTableau_p master, Clause_p clause, PStack_p local_variables)
{
	Clause_p new_clause = NULL;
	assert(PStackGetSP(local_variables));
	assert(clause->set);
	Subst_p subst = SubstAlloc();
	ClauseSet_p label_storage = clause->set;
	for (PStackPointer p = 0; p < PStackGetSP(local_variables); p++)
	{
		Term_p old_var = PStackElementP(local_variables, p);
		assert(old_var);
		assert(old_var->f_code < 0);
		assert(!(old_var->binding));
		Term_p fresh_var = ClauseTableauGetFreshVar(master->master, old_var);
		assert(fresh_var != old_var);
		assert(old_var->f_code != fresh_var->f_code);
		SubstAddBinding(subst, old_var, fresh_var);
	}
	new_clause = ClauseCopy(clause, master->terms);
	ClauseSetInsert(label_storage, new_clause);
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
	if (num_vars == 0)
	{
		PTree_p temp = NULL;
		ClauseCollectVariables(branch->label, &temp);
		PTreeFree(temp);
	}
	if (local_vars == num_vars)
	{
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

void ClauseTableauCollectVariables(ClauseTableau_p tab, PTree_p *variables)
{
	ClauseTableau_p branch = tab->open_branches->anchor->succ;
	while (branch != tab->open_branches->anchor)
	{
		CollectVariablesOfBranch(branch, variables, true);
		branch = branch->succ;
	}
}

/*
** Update the local variables of tab
*/

void ClauseTableauUpdateVariables(ClauseTableau_p tab)
{
	assert(tab);
	PTree_p tableau_variables = NULL;
	if (tab->tableau_variables)
	{
		PTreeFree(tab->tableau_variables);
	}
	ClauseTableauCollectVariables(tab, &tableau_variables);
	tab->tableau_variables = tableau_variables;
}
