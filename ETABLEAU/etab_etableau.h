#ifndef ETABLEAU
#define ETABLEAU
#include "etab_foldingup.h"
#include "etab_xgboost_interaction.h"

ErrorCodes EproverCloseBranch(ProofState_p proofstate,
                              ProofControl_p proofcontrol,
                              ClauseTableau_p branch,
                              long max_proc);
ErrorCodes EproverCloseBranchWrapper(ProofState_p proofstate,
                                     ProofControl_p proofcontrol,
                                     ClauseTableau_p branch,
                                     TableauControl_p tableau_control,
                                     long max_proc);
int CloseBranchesWithEprover(TableauControl_p tableau_control,
                             ClauseTableau_p tableau,
                             long max_proc);

ErrorCodes ProcessSpecificClauseWrapper(ProofState_p state,
                                       ProofControl_p control,
                                       Clause_p clause,
                                       Clause_p *success_ref);

ErrorCodes ProcessSpecificClauseStack(ProofState_p state,
                                      ProofControl_p control,
                                      ClauseStack_p stack,
                                      Clause_p *success_ref);

bool EtableauSaturateAllTableauxInStack(TableauControl_p tableaucontrol,
                                        TableauStack_p distinct_tableaux_stack,
                                        ClauseSet_p active,
                                        long maximum);

ProofState_p EtableauUpdateSaturationState(ClauseTableau_p leaf);

#endif
