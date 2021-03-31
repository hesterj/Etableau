#include "etab_localunification.h"

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
    assert(NodeIsLeaf(node));
    assert(node->set);
    assert(node->set == node->open_branches);

    PTreeFree(node->local_variables);

    // Collect the variables of our branch
    num_variables += CollectVariablesOfBranch(node, &local_variables_tree, true);

    // Collect the variables of the other branches
    ClauseTableau_p branch_iterator = node->open_branches->anchor->succ;
    PTree_p temp_variable_tree = NULL;
    while (branch_iterator != node->open_branches->anchor)
    {
        //if ((int) floor(GetTotalCPUTime())%2 == 0)
        //{
            //printf("iter %p %f\n", node, GetTotalCPUTime());
        //}
        if (branch_iterator != node)
        {
            CollectVariablesOfBranch(branch_iterator, &temp_variable_tree, true); // We need to include the root, otherwise branches could share variables there...
        }
        branch_iterator = branch_iterator->succ;
    }

// Remove the variables of other branches from the tree of branch variables
    PTreeComplement(&(local_variables_tree), temp_variable_tree);
    PTreeFree(temp_variable_tree);
    node->local_variables = local_variables_tree;

    return PTreeNodes(node->local_variables);
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

   for (PStackPointer p=0; p<PStackGetSP(node->old_labels); p++)
   {
	   Clause_p old_label = (Clause_p) PStackElementP(node->old_labels, p);
	   num_collected += ClauseCollectVariables(old_label, var_tree);
   }
	
   Clause_p handle;
   if (node->folding_labels)
   {
	   for(handle = node->folding_labels->anchor->succ; handle!= node->folding_labels->anchor; handle =
			  handle->succ)
	   {
		  num_collected += ClauseCollectVariables(handle, var_tree);
	   }
   }

   for (PStackPointer p=0; p<PStackGetSP(node->old_folding_labels); p++)
   {
	   ClauseSet_p old_fold_label_set = (ClauseSet_p) PStackElementP(node->old_folding_labels, p);
	   Clause_p fold_handle;
	   for(fold_handle = old_fold_label_set->anchor->succ; fold_handle != old_fold_label_set->anchor; fold_handle =
			  fold_handle->succ)
	   {
		  num_collected += ClauseCollectVariables(fold_handle, var_tree);
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

long ReplaceLocalVariablesWithFreshSubst(ClauseTableau_p master, Clause_p clause, PTree_p local_variables, Subst_p subst)
{
    assert(local_variables);
    assert(master->master == master);

    PTree_p clause_variables = NULL;
    long number_of_clause_variables __attribute__((unused)) = ClauseCollectVariables(clause, &(clause_variables));
    long number_of_nonlocal_in_clause __attribute__((unused))  = PTreeDestrIntersection(&(clause_variables), local_variables);

    Term_p old_var = NULL;

    while ((old_var = (Term_p) PTreeExtractRootKey(&clause_variables)))
    {
        ClauseTableauBindFreshVar(master, subst, old_var);
    }

    PTreeFree(clause_variables);
    return number_of_nonlocal_in_clause;
}

// Only call this after the local variables of the tableau have been updated.

bool VarIsLocal(ClauseTableau_p open_branch, Term_p variable)
{
	Warning("Not implemented (VarIsLocal)");
	return false;
}

/*  Only call this method if the local variables of the tableau have been udpated!
 *  This method deletes the substitution used in the replacement.
*/

Clause_p ReplaceLocalVariablesWithFresh(ClauseTableau_p master, Clause_p clause, PStack_p local_variables)
{
    assert(master->master == master);
    assert(PStackGetSP(local_variables));
    assert(clause->set);
    assert(ClauseLiteralNumber(clause));
    Clause_p new_clause = NULL;
    Subst_p subst = SubstAlloc();
    ClauseSet_p label_storage = clause->set;
    for (PStackPointer p = 0; p < PStackGetSP(local_variables); p++)
    {
        Term_p old_var = PStackElementP(local_variables, p);
        assert(old_var);
        assert(old_var->f_code < 0);
        assert(!(old_var->binding));
        ClauseTableauBindFreshVar(master, subst, old_var);
    }
    new_clause = ClauseCopy(clause, master->terms);
    ClauseSetInsert(label_storage, new_clause);
    SubstDelete(subst);
    assert(new_clause);
    assert(new_clause->literals);
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

// Collects variables occurring in all OPEN branches.

void ClauseTableauCollectVariables(ClauseTableau_p tab, PTree_p *variables)
{
	ClauseTableau_p branch = tab->open_branches->anchor->succ;
	while (branch != tab->open_branches->anchor)
	{
		CollectVariablesOfBranch(branch, variables, true);
		branch = branch->succ;
	}
}

// Collects variables occurring in ALL branches.

void ClauseTableauCollectVariables2(ClauseTableau_p tab, PTree_p *variables)
{
	PStack_p leaves = PStackAlloc();
	ClauseTableauCollectLeavesStack(tab->master, leaves);
	for (PStackPointer p=0; p<PStackGetSP(leaves); p++)
	{
		ClauseTableau_p branch = PStackElementP(leaves, p);
		CollectVariablesOfBranch(branch, variables, true);
	}
	//while (branch != tab->open_branches->anchor)
	//{
		//CollectVariablesOfBranch(branch, variables, true);
		//branch = branch->succ;
	//}
	PStackFree(leaves);
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
	//ClauseTableauCollectVariables(tab, &tableau_variables);
	ClauseTableauCollectVariables2(tab, &tableau_variables);
	tab->tableau_variables = tableau_variables;
}

/*-----------------------------------------------------------------------
//
// Function: PTreeComplement()
//
// Find the complement of tree2 in tree1.
// Remove the elements of tree1 that are found in tree2.
// Changes tree1, does not affect tree2.
//
// Global Variables: -
//
// Side Effects    : Memory operations
//
/----------------------------------------------------------------------*/

long PTreeComplement(PTree_p *tree1, PTree_p tree2)
{
   PTree_p tmp = NULL;
   void* key;
   long res = 0;

   while((key = PTreeExtractRootKey(tree1)))
   {
      if(!PTreeFindBinary(tree2, key))
      {
         PTreeStore(&tmp, key);
      }
   }
   assert(!(*tree1));
   *tree1 = tmp;

   return res;
}
