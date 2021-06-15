#include "etab_localunification.h"

void reset_variables_array(PDArray_p variables_array);
long union_variables_array(PDArray_p larger, PDArray_p smaller);
long union_variables_branch(ClauseTableau_p branch, PDArray_p array);
long delete_variables_from_other(PDArray_p array, PDArray_p other);

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

//long UpdateLocalVariables(ClauseTableau_p node)
//{
    //PTree_p local_variables_tree = NULL;
    //assert(NodeIsLeaf(node));
    //assert(node->set);
    //assert(node->set == node->open_branches);
//
    //PTreeFree(node->local_variables);
//
    //// Collect the variables of our branch
    //node->number_of_variables_on_branch =
        //CollectVariablesOfBranch(node, &local_variables_tree, true);
//
    //// Collect the variables of the other branches
    //ClauseTableau_p branch_iterator = node->open_branches->anchor->succ;
    //PTree_p temp_variable_tree = NULL;
    //while (branch_iterator != node->open_branches->anchor)
    //{
        //if (branch_iterator != node)
        //{
            //// We need to include the root, otherwise branches could share variables there
            //branch_iterator->number_of_variables_on_branch =
                //CollectVariablesOfBranch(branch_iterator, &temp_variable_tree, true);
        //}
        //branch_iterator = branch_iterator->succ;
    //}
//
//// Remove the variables of other branches from the tree of branch variables
    //PTreeComplement(&(local_variables_tree), temp_variable_tree);
    //PTreeFree(temp_variable_tree);
    //node->local_variables = local_variables_tree;
//
    //return PTreeNodes(node->local_variables);
//}

/*  This method updates the local variables of the node.
 * This is intended to be used on the leaf node of a branch.
 * Variables that are local (do not occur on any open branch but
 * this one) can be treated with the local extension rule and local
 * reduction rule.
 *
 *   The method returns the number of local variables for node's
 * branch.  The local variables tree of node is deleted if it
 * exists.
*/

long UpdateLocalVariables2(ClauseTableau_p node)
{
    assert(NodeIsLeaf(node));
    assert(node->set);
    assert(node->set == node->open_branches);

    long res = 0;
    PDArray_p branch_variables = PDArrayAlloc(4,4);
    PDArray_p other_variables = PDArrayAlloc(4,4);
    ClauseTableau_p branch_iterator = node->open_branches->anchor->succ;

    union_variables_branch(node, branch_variables);
    node->number_of_variables_on_branch = PDArrayMembers(branch_variables);

    while (branch_iterator != node->open_branches->anchor)
    {
        if (branch_iterator != node)
        {
            union_variables_branch(branch_iterator, other_variables);
        }
        branch_iterator = branch_iterator->succ;
    }

    res = delete_variables_from_other(branch_variables, other_variables);

    // To maintain compatibility with original method, this is probably better done with an array.
    PTreeFree(node->local_variables);
    node->local_variables = NULL;
    for (long i=0; i<branch_variables->size; i++)
    {
        if (PDArrayElementP(branch_variables, i))
        {
            PTreeStore(&(node->local_variables), PDArrayElementP(branch_variables, i));
        }
    }
#ifndef NDEBUG
    if (res != PTreeNodes(node->local_variables))
    {
        printf("%ld %ld\n", res, PTreeNodes(node->local_variables));
    }
    assert(res == PTreeNodes(node->local_variables));
#endif
    //

    PDArrayFree(branch_variables);
    PDArrayFree(other_variables);
    return res;
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

/*  Returns number of variables found
 *
*/

long CollectVariablesOfBranchArray(ClauseTableau_p branch, PDArray_p array, bool include_root)
{
    long num_variables = 0;
    ClauseTableau_p iterator = branch;
    while (iterator)
    {
        if ((iterator != branch->master) || (include_root))
        {
            num_variables += CollectVariablesAtNodeArray(iterator, array);
        }
        iterator = iterator->parent;
    }
    return num_variables;
}

/*  Returns number of variables found
 *  Uses node_variables_array
*/

long CollectVariablesOfBranchArray2(ClauseTableau_p branch, PDArray_p array, bool include_root)
{
    long num_variables = 0;
    ClauseTableau_p iterator = branch;
    PDArray_p node_variables_array = NULL;
    while (iterator)
    {
        // If the node has alreay been visited and the variables collected, it is marked with TUPSpecialFlag
        if (ClauseTableauQueryProp(iterator, TUPSpecialFlag))
        {
            break;
        }
        node_variables_array = iterator->node_variables_array;
        reset_variables_array(node_variables_array);
        assert(node_variables_array);
        num_variables += CollectVariablesAtNodeArray(iterator, node_variables_array); // Collect the variables here
        union_variables_array(array, node_variables_array); // Add the nodes here to the tableau variables array
        ClauseTableauSetProp(iterator, TUPSpecialFlag); // Block this node from having variables collected again
        iterator = iterator->parent;
    }
    return num_variables;
}

/*  At a node in a tableau, there are folding_labels, the label itself, and 
 * unit axioms at the root node.  This method collects all the variables of the aforementioned in to tree.  The number of
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
       for(handle = node->folding_labels->anchor->succ;
           handle!= node->folding_labels->anchor;
           handle = handle->succ)
       {
           num_collected += ClauseCollectVariables(handle, var_tree);
       }
   }

   return num_collected;
}

/*  At a node in a tableau, there are folding_labels, the label itself, and
 * unit axioms at the root node.  This method collects all the variables of the aforementioned in to array.  The number of
 * variables found is returned.
*/

long CollectVariablesAtNodeArray(ClauseTableau_p node, PDArray_p array)
{
   long num_collected = 0;
   assert(node);
   assert(node->label);

   num_collected += ClauseCollectVariablesArray(node->label, array);

   Clause_p handle;
   if (node->folding_labels)
   {
       for(handle = node->folding_labels->anchor->succ;
           handle!= node->folding_labels->anchor;
           handle = handle->succ)
       {
           num_collected += ClauseCollectVariablesArray(handle, array);
       }
   }

   return num_collected;
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
    Error("Not implemented (VarIsLocal)", 100);
    return false;
}

/*  Return true if the branch is local
 *  Side Effect: Updates local variables of branch
*/

bool BranchIsLocal(ClauseTableau_p branch)
{
    //long local_variables = UpdateLocalVariables(branch);
    long local_variables = UpdateLocalVariables2(branch);

    // CollectVariableOfBranch was used here before but didn't work
    if (local_variables == branch->number_of_variables_on_branch)
    {
        return true;
    }
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

// Collects variables occurring in ALL branches.

//void ClauseTableauUpdateVariablesArray(ClauseTableau_p tab)
//{
    //assert(tab == tab->master);
    //PDArray_p array = tab->tableau_variables_array;
    //reset_variables_array(array);
    //ClauseTableau_p branch = tab->open_branches->anchor->succ;
    //while (branch != tab->open_branches->anchor)
    //{
        //CollectVariablesOfBranchArray(branch, array, true);
        //branch = branch->succ;
    //}
//}

// Collects variables occurring in ALL branches.  Uses node_variables_array, unlike this function's counterpart

void ClauseTableauUpdateVariablesArray2(ClauseTableau_p tab)
{
    assert(tab == tab->master);
    PDArray_p tableau_variables_array = tab->tableau_variables_array;
    reset_variables_array(tableau_variables_array);
    ClauseTableauDeleteFlag(tab, TUPSpecialFlag); // Delete TUPSpecialFlag at all nodes
    ClauseTableau_p branch = tab->open_branches->anchor->succ;
    while (branch != tab->open_branches->anchor)
    {
        CollectVariablesOfBranchArray2(branch, tableau_variables_array, true);
        branch = branch->succ;
    }
    ClauseTableauDeleteFlag(tab, TUPSpecialFlag); // Delete TUPSpecialFlag at all nodes
}

void reset_variables_array(PDArray_p variables_array)
{
    assert(variables_array);
    for (long i=0; i<variables_array->size; i++)
    {
        PDArrayAssignP(variables_array, i, NULL);
    }
}

// Add all of the non-NULL values of smaller to larger at the same index
// Returns the number of values set.

long union_variables_array(PDArray_p larger, PDArray_p smaller)
{
    assert(larger);
    assert(smaller);
    long new = 0;
    for (long i=0; i<smaller->size; i++)
    {
        if (PDArrayElementP(smaller, i))
        {
            PDArrayAssignP(larger, i, PDArrayElementP(smaller, i));
            new++;
        }
    }
    return new;
}

// Union all of the variables on branch in to array

long union_variables_branch(ClauseTableau_p branch, PDArray_p array)
{
    assert(branch);
    assert(array);
    ClauseTableau_p iterator = branch;
    long number_of_variables_on_branch = 0;
    while (iterator)
    {
        assert(iterator->node_variables_array);
        number_of_variables_on_branch += union_variables_array(array, iterator->node_variables_array);
        iterator = iterator->parent;
    }
    return number_of_variables_on_branch;
}

// Iterate over array, if non-NULL occurs in array and other at the same index, delete it from array.
// Returns the number of non-NULL entries remaining in array.

long delete_variables_from_other(PDArray_p array, PDArray_p other)
{
    assert(array);
    assert(other);
    long res = 0;
    for (long i=0; i<array->size; i++)
    {
        if (PDArrayElementP(array, i))
        {
            if (PDArrayElementP(other, i))
            {
                assert(PDArrayElementP(array,i) == PDArrayElementP(other, i));
                PDArrayAssignP(array, i, NULL);
            }
            else
            {
                res++;
            }
        }
    }
    return res;
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
