#ifndef ETAB_NEWPROC
#define ETAB_NEWPROC
#include<etab_tableauproc.h>


int Etableau_n0(TableauControl_p tableaucontrol,
               ProofState_p proofstate,
               ProofControl_p proofcontrol,
               TB_p bank,
               ClauseSet_p active,
               unsigned long max_depth,
               int tableauequality);

bool EtableauMultiprocess(TableauControl_p tableaucontrol,
                            PStack_p starting_tableaux,
                            ClauseSet_p active,
                            ClauseSet_p extension_candidates,
                            unsigned long max_depth);

bool EtableauSelectTableau(TableauControl_p tableaucontrol,
                            TableauStack_p distinct_tableaux_stack,
                            ClauseSet_p active,
                            ClauseSet_p extension_candidates);

bool EtableauPopulation(TableauControl_p tableaucontrol,
                        TableauStack_p distinct_tableaux_stack,
                        ClauseSet_p active,
                        ClauseSet_p extension_candidates,
                        TableauStack_p new_tableaux);

ClauseTableau_p EtableauSelectBranchAndExtend(TableauControl_p tableaucontrol,
                                              ClauseTableau_p state,
                                              ClauseSet_p extension_candidates,
                                              BacktrackStatus_p backtrack_status);

ClauseTableau_p EtableauPopulationSelectBranchAndExtend(TableauControl_p tableaucontrol,
                                                        ClauseTableau_p state,
                                                        ClauseSet_p extension_candidates,
                                                        BacktrackStatus_p backtrack_status,
                                                        TableauStack_p new_tableaux);

#endif
