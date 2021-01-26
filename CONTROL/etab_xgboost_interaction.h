#ifndef ETAB_XGBOOST
#define ETAB_XGBOOST

#include "etab_foldingup.h"
//#include </home/hesterj/Projects/xgboost/include/xgboost/c_api.h>

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
void DTreeFree(void *trash);
DTree_p DTreeRepresentation(Term_p term);
int DTreesIdentical(const void *left, const void *right); // ComparisonFunctionType
//DTree_p PTreeFindDTree(QuadTree_p *splay_tree, DTree_p dtree);
DTree_p DTreeEqnRepresentation(Eqn_p eqn);
void FeatureTreePrint(FILE* out, PObjTree_p *tree_of_trees);

long DTreeBranchRepresentations(ClauseTableau_p branch, PObjTree_p *tree_of_trees);
long EqnBranchRepresentations(ClauseTableau_p branch, PObjTree_p *tree_of_eqns);
void DTreeResetOccurrences(void *tree);
void ResetAllOccurrences(PObjTree_p *tree_of_trees);

void DTreeStupidPrint(DTree_p root);
void DTreeStupidPrintChildren(DTree_p root);

bool EqnUnifyRenamingP(Eqn_p left, Eqn_p right);
int EqnUnifyRenamingPCmp(const void *left_p, const void *right_p);
void EqnTreePrint(FILE* out, PObjTree_p *tree_of_eqns);
void EqnPListPrint(FILE* out, PList_p list_of_eqns);
long EqnBranchRepresentationsList(ClauseTableau_p branch, PList_p list_of_eqns, int branch_status);
Eqn_p EquivalentEquationInList(Eqn_p eqn, PList_p anchor);

//void XGBoostTest();
#endif
