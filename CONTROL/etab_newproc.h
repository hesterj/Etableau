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
bool EtableauMultiprocess_n(TableauControl_p tableaucontrol,
                            PStack_p starting_tableaux,
                            ClauseSet_p active,
                            ClauseSet_p extension_candidates,
                            unsigned long max_depth);
bool EtableauProofSearch_n1(TableauControl_p tableaucontrol,
                            TableauStack_p distinct_tableaux_stack,
                            ClauseSet_p active,
                            ClauseSet_p extension_candidates);
bool EtableauPopulate_n1(TableauControl_p tableaucontrol,
                         TableauStack_p distinct_tableaux_stack,
                         ClauseSet_p active,
                         ClauseSet_p extension_candidates,
                         TableauStack_p new_tableaux);
//ClauseTableau_p EtableauProofSearch_n2(TableauControl_p tableaucontrol,
                                       //ClauseTableau_p master,
                                       //ClauseSet_p extension_candidates,
                                       //int max_depth,
                                       //BacktrackStatus_p status);
//ClauseTableau_p EtableauPopulate_n2(TableauControl_p tableaucontrol,
                                    //ClauseTableau_p master,
                                    //ClauseSet_p extension_candidates,
                                    //BacktrackStatus_p status,
                                    //TableauStack_p new_tableaux);
ClauseTableau_p EtableauProofSearch_n3(TableauControl_p tableaucontrol,
                                       ClauseTableau_p state,
                                       ClauseSet_p extension_candidates,
                                       BacktrackStatus_p backtrack_status);
ClauseTableau_p EtableauPopulate_n3(TableauControl_p tableaucontrol,
                                    ClauseTableau_p state,
                                    ClauseSet_p extension_candidates,
                                    BacktrackStatus_p backtrack_status,
                                    TableauStack_p new_tableaux);
#endif
