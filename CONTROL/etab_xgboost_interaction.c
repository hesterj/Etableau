#include"etab_xgboost_interaction.h"

DTree_p DTreeAlloc(long key, int arity)
{
    DTree_p handle = DTreeCellAlloc();
    handle->key = key;
    handle->arity = arity;
    handle->children = DTreeArgArrayAlloc(arity);
    for (int i=0; i<arity; i++)
    {
        handle->children[i] = NULL;
    }
    return handle;
}

void DTreeFree(DTree_p trash)
{
    DTree_p *children = trash->children;
    int arity = trash->arity;
    DTreeCellFree(trash);
    for (int i=0; i<arity; i++)
    {
        DTreeFree(children[i]);
    }
    DTreeArgArrayFree(children, arity);
}

DTree_p DTreeRepresentation(Term_p term)
{
    assert(term);
    int arity = term->arity;
    long code = TermIsVar(term) ? -1 : term->f_code;
    DTree_p handle = DTreeAlloc(code, term->arity);
    if (arity)
    {
        handle->children = DTreeArgArrayAlloc(arity);
        for (int i=0; i<arity; i++)
        {
            handle->children[i] = DTreeRepresentation(term->args[i]);
        }
    }

    return handle;
}

DTree_p DTreeEqnRepresentation(Eqn_p eqn)
{
    bool positive = EqnIsPositive(eqn);
    DTree_p handle = DTreeAlloc(positive, 2);
    handle->children = DTreeArgArrayAlloc(2);
    handle->children[0] = DTreeRepresentation(eqn->lterm);
    handle->children[1] = DTreeRepresentation(eqn->rterm);
    return handle;

}

// Return 0 if the two DTree_p are identical
// This is intended to be a ComparisonFunctionType!

int DTreesIdentical(const void *left_p, const void *right_p)
{
    DTree_p left = (DTree_p) left_p;
    DTree_p right = (DTree_p) right_p;
    if (left->key != right->key || left->arity != right->arity) return 1;
    int arity = left->arity;
    int children_identical = 0;
    for (int i=0; i<arity; i++)
    {
        children_identical = DTreesIdentical(left->children[i], right->children[i]);
        if (children_identical != 0) return 1;
    }
    return 0;
}


// This commented out function shouldn't be necessary due to the benefits of PObjTree_p

//DTree_p PTreeFindDTree(PObjTree_p *splay_tree, DTree_p dtree)
//{
   //PStack_p iter = QuadTreeTraverseInit(*splay_tree);
   //QuadTree_p  handle = NULL;
//
   //while((handle = QuadTreeTraverseNext(iter)))
   //{
       //if (DTreesIdentical(handle->p1, dtree))
       //{
           //QuadTreeTraverseExit(iter);
           //return handle->p1;
       //}
   //}
//
   //QuadTreeTraverseExit(iter);
   //return NULL;
//}

/*
** This is the function that gets (an easy) feature representation of the branch.  Features are indexed by their address of the corresponding DTree_p.
** The number of occurrences of a feature is the value of the occurence_function applied to the memory addresses of the branch's DTree_p occurrences.
 */

long DTreeBranchRepresentations(ClauseTableau_p branch, PObjTree_p *tree_of_trees)
{
    while (branch != branch->master)
    {
        assert(ClauseLiteralNumber(branch->label) == 1);
        PObjTree_p new_cell = PTreeCellAlloc();
        Eqn_p label_eqn = branch->label->literals;
        DTree_p dtree_representation = DTreeEqnRepresentation(label_eqn);
        new_cell->key = dtree_representation;
        //PObjTree_p objtree_cell = PTreeObjStore(tree_of_trees, dtree_representation, DTreesIdentical);
        PObjTree_p objtree_cell = PTreeObjInsert(tree_of_trees, new_cell, DTreesIdentical);
        if (objtree_cell) // We found a cell with an identical ptree, so we can discard the one we just made and increment the number of occurrences of the one we found.
        {
            PTreeCellFree(new_cell);
            DTreeFree(dtree_representation);
            DTree_p real_tree = (DTree_p) objtree_cell->key;
            real_tree->occurrences++;
            fprintf(GlobalOut, "%p: %d\n", real_tree, real_tree->occurrences);
        }
        else // The dtree we just made has been inserted into the tree of dtrees, and since it clearly occurs we increment the occurrences.
        {
            dtree_representation->occurrences++;
            fprintf(GlobalOut, "%p: %d\n", dtree_representation, dtree_representation->occurrences++);
        }

        branch = branch->parent;
    }
    return 0;
}

void DTreeResetOccurrences(void *tree)
{
    DTree_p tree_casted = (DTree_p) tree;
    tree_casted->occurrences = 0;
}
void ResetAllOccurrences(PObjTree_p *tree_of_trees)
{
    PTreeVisitInOrder(*tree_of_trees, DTreeResetOccurrences);
}
