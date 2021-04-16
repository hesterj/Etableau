#ifndef ETABLEAU
#define ETABLEAU
#include "etab_foldingup.h"
#include "etab_xgboost_interaction.h"

ErrorCodes ECloseBranch(ProofState_p proofstate,
                        ProofControl_p proofcontrol,
                        ClauseTableau_p branch,
                        long max_proc);
ErrorCodes ECloseBranchWrapper(ProofState_p proofstate,
                               ProofControl_p proofcontrol,
                               ClauseTableau_p branch,
                               TableauControl_p tableau_control,
                               long max_proc);
int AttemptToCloseBranchesWithSuperposition(TableauControl_p tableau_control,
                                             ClauseTableau_p tableau,
                                             long max_proc);

int ProcessSpecificClauseWrapperNoCopy(ProofState_p state,
                                       ProofControl_p control,
                                       Clause_p clause,
                                       Clause_p *success_ref);

ErrorCodes ProcessSpecificClauseStackWrapperNoCopy(ProofState_p state,
                                                   ProofControl_p control,
                                                   ClauseStack_p stack,
                                                   Clause_p *success_ref);

bool EtableauSaturateAllTableauxInStack(TableauControl_p tableaucontrol,
                                        TableauStack_p distinct_tableaux_stack,
                                        ClauseSet_p active,
                                        long maximum);

#endif
