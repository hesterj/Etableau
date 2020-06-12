#ifndef LOCALUNI
#define LOCALUNI

#include <clausetableaux.h>

long UpdateLocalVariables(ClauseTableau_p node);
long CollectVariablesAtNode(ClauseTableau_p node, PTree_p *var_tree);
long CollectVariablesOfBranch(ClauseTableau_p branch, PTree_p *branch_vars, bool include_root);
bool BranchIsLocal(ClauseTableau_p branch);
bool AllBranchesAreLocal(ClauseTableau_p master);
Clause_p ReplaceLocalVariablesWithFresh(ClauseTableau_p master, Clause_p clause, PStack_p local_variables);

#endif
