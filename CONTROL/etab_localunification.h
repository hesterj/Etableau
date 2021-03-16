#ifndef LOCALUNI
#define LOCALUNI

#include "etab_clausetableaux.h"

long UpdateLocalVariables(ClauseTableau_p node);
long CollectVariablesAtNode(ClauseTableau_p node, PTree_p *var_tree);
long CollectVariablesOfBranch(ClauseTableau_p branch, PTree_p *branch_vars, bool include_root);
bool BranchIsLocal(ClauseTableau_p branch);
bool AllBranchesAreLocal(ClauseTableau_p master);
Clause_p ReplaceLocalVariablesWithFresh(ClauseTableau_p master, Clause_p clause, PStack_p local_variables);
Clause_p ReplaceLocalVariablesWithFreshSubst(ClauseTableau_p master, Clause_p clause, PStack_p local_variables, Subst_p subst);

void ClauseTableauCollectVariables(ClauseTableau_p tab, PTree_p *variables);
void ClauseTableauUpdateVariables(ClauseTableau_p tab);

#endif
