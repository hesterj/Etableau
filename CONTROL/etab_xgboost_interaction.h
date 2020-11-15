#ifndef ETAB_XGBOOST
#define ETAB_XGBOOST

#include <etab_foldingup.h>

/*
** The DTree is just that, a tree of integers, with potentially multiple children.
** These are meant to be tree representation of terms.
*/

typedef struct dtree
{
    long key;
    int arity;
    struct dtree* *children;
}DTree, *DTree_p;


#define DTreeCellAlloc() (DTree*)SizeMalloc(sizeof(DTree))
#define DTreeCellFree(junk) SizeFree(junk, sizeof(DTree))
#define DTreeArgArrayAlloc(arity) ((DTree_p*)SizeMalloc((arity)*sizeof(DTree_p)))
#define DTreeArgArrayFree(junk, arity) SizeFree((junk),(arity)*sizeof(DTree_p))
DTree_p DTreeAlloc(long key, int arity);
void DTreeFree(DTree_p trash);
DTree_p DTreeRepresentation(Term_p term);
bool PTreeFindDTree(PTree_p splay_tree, DTree_p dtree);
DTree_p DTreeEqnRepresentation(Eqn_p eqn);

#endif
