#ifndef CLOSURE
#define CLOSURE

#include <localunification.h>

bool ClauseTableauBranchClosureRuleWrapper(ClauseTableau_p tab);
int AttemptClosureRuleOnAllOpenBranches(ClauseTableau_p tableau);
Subst_p ClauseContradictsBranch(ClauseTableau_p tab, Clause_p clause);
Subst_p ClauseContradictsSet(ClauseTableau_p tab, Clause_p leaf, ClauseSet_p set, ClauseTableau_p open_branch);

#endif
