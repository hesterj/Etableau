#ifndef FOLDINGUP
#define FOLDINGUP

#include "etab_closure.h"

#define NO_CHILDREN_CLOSED_BY_SATURATION 0
#define CHILD_CLOSED_BY_SATURATION 1
#define CHILDREN_CLOSED_BY_SATURATION_ALLOWED 2

bool ClauseTableauMarkClosedNodes(ClauseTableau_p tableau, int *subtree_saturation_closed);
#define ClauseTableauNodeIsClosed(tab) ClauseTableauMarkClosedNodes(tab, NULL)

PStack_p CollectDominatedMarkingsWrapper(ClauseTableau_p tableau);
void CollectDominatedMarkings(ClauseTableau_p original, ClauseTableau_p tableau, PStack_p stack);

PStack_p NodesThatDominateTableauFromMarks(ClauseTableau_p tableau, PStack_p marks);

Clause_p FoldingUpGetLabelFromMark(ClauseTableau_p tableau, int mark);
ClauseTableau_p FoldingUpGetNodeFromMark(ClauseTableau_p tableau, int mark);

ClauseTableau_p PStackGetDeepestTableauNode(PStack_p stack);

int FoldUpAtNode(ClauseTableau_p node);
int FoldUpEveryNodeOnce(ClauseTableau_p tableau);

int FoldUpCloseCycle(ClauseTableau_p tableau);

void ClauseTableauEdgeInsert(ClauseTableau_p edge, Clause_p clause);

#endif
