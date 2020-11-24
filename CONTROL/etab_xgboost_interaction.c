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

void DTreeFree(void *trash_tree)
{
    DTree_p trash = (DTree_p) trash_tree;
    DTree_p *children = trash->children;
    int arity = trash->arity;
    for (int i=0; i<arity; i++)
    {
        DTreeFree(children[i]);
    }
    DTreeCellFree(trash);
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
void DTreeStupidPrintChildren(DTree_p root)
{
    for (int i=0; i<root->arity; i++)
    {
        DTree_p child = root->children[i];
        fprintf(GlobalOut, "%ld ", child->key);
    }
    fprintf(GlobalOut, "\n");
    for (int i=0; i<root->arity; i++)
    {
        DTreeStupidPrintChildren(root->children[i]);
    }

}

void DTreeStupidPrint(DTree_p root)
{
    fprintf(GlobalOut, "%ld\n", root->key);
    for (int i=0; i<root->arity; i++)
    {
        DTreeStupidPrintChildren(root->children[i]);
    }
}

/*
** This is the function that gets (an easy) feature representation of the branch.  Features are indexed by their address of the corresponding DTree_p.
** The number of occurrences of a feature is the value of the occurence_function applied to the memory addresses of the branch's DTree_p occurrences.
 */

long DTreeBranchRepresentations(ClauseTableau_p branch, PObjTree_p *tree_of_trees)
{
    //fprintf(GlobalOut, "# getting branch representations\n");
    //fprintf(GlobalOut, "# p: %p\n", *tree_of_trees);
    while (branch != branch->master)
    {
        assert(ClauseLiteralNumber(branch->label) == 1);
        PObjTree_p new_cell = PTreeCellAlloc();
        Eqn_p label_eqn = branch->label->literals;
        DTree_p dtree_representation = DTreeEqnRepresentation(label_eqn);
        new_cell->key = dtree_representation;
        //fprintf(GlobalOut, "# inserting... &%p %p\n", tree_of_trees, *tree_of_trees);
        PObjTree_p objtree_cell = PTreeObjInsert(tree_of_trees, new_cell, DTreesIdentical);
        //fprintf(GlobalOut, "# done inserting\n");
        if (objtree_cell) // We found a cell with an identical ptree, so we can discard the one we just made and increment the number of occurrences of the one we found.
        {
            PTreeCellFree(new_cell);
            DTreeFree(dtree_representation);
            DTree_p real_tree = (DTree_p) objtree_cell->key;
            real_tree->occurrences++;
            *tree_of_trees = objtree_cell;  // The tree was splayed and objtree_cell is the new root.
        }
        else // The dtree we just made has been inserted into the tree of dtrees, and since it clearly occurs we increment the occurrences.
        {
            *tree_of_trees = new_cell; // Since the new cell was inserted into the splay tree, we need to ensure we have a reference to the root.
            dtree_representation->occurrences++;
        }

        branch = branch->parent;
    }
    //fprintf(GlobalOut, "# blablabla %ld\n", PTreeNodes(*tree_of_trees));
    return 0;
}

long EqnBranchRepresentations(ClauseTableau_p branch, PObjTree_p *tree_of_eqns)
{
    //fprintf(GlobalOut, "# getting branch representations\n");
    //fprintf(GlobalOut, "# p: %p\n", *tree_of_trees);
    while (branch != branch->master)
    {
        assert(ClauseLiteralNumber(branch->label) == 1);
        PObjTree_p new_cell = PTreeCellAlloc();
        Eqn_p label_eqn = branch->label->literals;
        DTree_p dtree_representation = DTreeEqnRepresentation(label_eqn);
        new_cell->key = dtree_representation;
        //fprintf(GlobalOut, "# inserting... &%p %p\n", tree_of_trees, *tree_of_trees);
        PObjTree_p objtree_cell = PTreeObjInsert(tree_of_eqns, new_cell, DTreesIdentical);
        //fprintf(GlobalOut, "# done inserting\n");
        if (objtree_cell) // We found a cell with an identical ptree, so we can discard the one we just made and increment the number of occurrences of the one we found.
        {
            PTreeCellFree(new_cell);
            DTreeFree(dtree_representation);
            DTree_p real_tree = (DTree_p) objtree_cell->key;
            real_tree->occurrences++;
            *tree_of_eqns = objtree_cell;  // The tree was splayed and objtree_cell is the new root.
        }
        else // The dtree we just made has been inserted into the tree of dtrees, and since it clearly occurs we increment the occurrences.
        {
            *tree_of_eqns = new_cell; // Since the new cell was inserted into the splay tree, we need to ensure we have a reference to the root.
            dtree_representation->occurrences++;
        }

        branch = branch->parent;
    }
    //fprintf(GlobalOut, "# blablabla %ld\n", PTreeNodes(*tree_of_trees));
    return 0;
}

bool EqnUnifyRenamingP(Eqn_p left, Eqn_p right)
{
    Subst_p subst = SubstAlloc();
    bool unified = EqnUnify(left, right, subst);
    if (!unified || !SubstIsRenaming(subst))
    {
        SubstDelete(subst);
        return false;
    }
    SubstDelete(subst);
    return true;
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


void FeatureTreePrint(FILE* out, PObjTree_p *tree_of_trees)
{
    PStack_p iter = PTreeTraverseInit(*tree_of_trees);
    PObjTree_p handle = NULL;
    while ((handle = PTreeTraverseNext(iter)))
    {
        DTree_p tree = (DTree_p) handle->key;
        assert(tree);
        fprintf(out, "# %p: %d\n", tree, tree->occurrences);
        DTreeStupidPrint(tree);
    }
    PTreeTraverseExit(iter);
}

