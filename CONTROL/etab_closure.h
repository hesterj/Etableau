#ifndef CLOSURE
#define CLOSURE

#include "etab_localunification.h"

bool ClauseTableauBranchClosureRuleWrapper(ClauseTableau_p tab);
int AttemptClosureRuleOnAllOpenBranches(ClauseTableau_p tableau);
Subst_p ClauseContradictsBranchSimple(ClauseTableau_p tab, Clause_p original_clause);
Subst_p ClauseContradictsSetSimple(ClauseTableau_p tab, Clause_p leaf, ClauseSet_p set, ClauseTableau_p open_branch);

#endif
