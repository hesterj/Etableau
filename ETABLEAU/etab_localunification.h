#ifndef LOCALUNI
#define LOCALUNI

#include "etab_clausetableaux.h"

long UpdateLocalVariables(ClauseTableau_p node);
long UpdateLocalVariables2(ClauseTableau_p node);
long CollectVariablesAtNode(ClauseTableau_p node, PTree_p *var_tree);
long CollectVariablesAtNodeArray(ClauseTableau_p node, PDArray_p array);
long CollectVariablesOfBranch(ClauseTableau_p branch, PTree_p *branch_vars, bool include_root);
bool BranchIsLocal(ClauseTableau_p branch);
long ReplaceLocalVariablesWithFreshSubst(ClauseTableau_p master, Clause_p clause, PTree_p local_variables, Subst_p subst);
bool VarIsLocal(ClauseTableau_p open_branch, Term_p variable);

void ClauseTableauUpdateVariablesArray(ClauseTableau_p tab);
void ClauseTableauUpdateVariablesArray2(ClauseTableau_p tab);
long CollectVariablesOfBranchArray(ClauseTableau_p branch, PDArray_p array, bool include_root);
long CollectVariablesOfBranchArray2(ClauseTableau_p branch, PDArray_p array, bool include_root);

long PTreeComplement(PTree_p *tree1, PTree_p tree2);

#endif
