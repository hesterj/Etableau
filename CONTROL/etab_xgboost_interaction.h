#ifndef ETAB_XGBOOST
#define ETAB_XGBOOST

#include "etab_foldingup.h"

/*
** The DTree is just that, a tree of integers, with potentially multiple children.
** These are meant to be tree representation of terms.
*/

typedef struct dtree
{
    long key;
    int arity;
    int occurrences; // This is for keeping the track multiple occurrences of a pattern within a branch.  Shouldn't happen but good to be ready...
    struct dtree* *children;
}DTree, *DTree_p;


#define DTreeCellAlloc() (DTree*)SizeMalloc(sizeof(DTree))
#define DTreeCellFree(junk) SizeFree(junk, sizeof(DTree))
#define DTreeArgArrayAlloc(arity) ((DTree_p*)SizeMalloc((arity)*sizeof(DTree_p)))
#define DTreeArgArrayFree(junk, arity) SizeFree((junk),(arity)*sizeof(DTree_p))
DTree_p DTreeAlloc(long key, int arity);
void DTreeFree(DTree_p trash);
DTree_p DTreeRepresentation(Term_p term);
int DTreesIdentical(const void *left, const void *right); // ComparisonFunctionType
DTree_p PTreeFindDTree(QuadTree_p *splay_tree, DTree_p dtree);
DTree_p DTreeEqnRepresentation(Eqn_p eqn);

long DTreeBranchRepresentations(ClauseTableau_p branch, PObjTree_p *tree_of_trees);
void DTreeResetOccurrences(void *tree);
void ResetAllOccurrences(PObjTree_p *tree_of_trees);

#endif
