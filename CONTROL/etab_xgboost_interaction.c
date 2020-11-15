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

bool DTreesIdentical(DTree_p left, DTree_p right)
{
    if (left->key != right->key || left->arity != right->arity) return false;
    int arity = left->arity;
    bool children_identical = true;
    for (int i=0; i<arity; i++)
    {
        children_identical = DTreesIdentical(left->children[i], right->children[i]);
        if (!children_identical) return false;
    }
    return true;
}

bool PTreeFindDTree(PTree_p splay_tree, DTree_p dtree)
{
   PStack_p iter = PTreeTraverseInit(splay_tree);
   PTree_p  handle = NULL;

   while((handle = PTreeTraverseNext(iter)))
   {
       if (DTreesIdentical(handle->key, dtree))
       {
           PTreeTraverseExit(iter);
           return true;
       }
   }

   PTreeTraverseExit(iter);
   return false;
}
