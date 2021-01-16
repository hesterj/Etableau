#ifndef ETAB_NEWPROC
#define ETAB_NEWPROC
#include<etab_tableauproc.h>


int Etableau_n0(TableauControl_p tableaucontrol,
               ProofState_p proofstate,
               ProofControl_p proofcontrol,
               TB_p bank,
               ClauseSet_p active,
               int max_depth,
               int tableauequality);

ClauseTableau_p EtableauProofSearch_n3(TableauControl_p tableaucontrol,
                                      ClauseTableau_p state,
                                      ClauseSet_p extension_candidates,
                                      int current_depth,
                                      int max_depth,
                                      BacktrackStatus_p backtrack_status,
                                      TableauStack_p new_tableaux);
bool EtableauMultiprocess_n(TableauControl_p tableaucontrol,
                            PStack_p starting_tableaux,
                            ClauseSet_p active,
                            ClauseSet_p extension_candidates,
                            int max_depth);
ClauseTableau_p EtableauProofSearchAtDepth_n2(TableauControl_p tableaucontrol,
                                             ClauseTableau_p master,
                                             ClauseSet_p extension_candidates,
                                             int max_depth,
                                             BacktrackStatus_p status,
                                             TableauStack_p new_tableaux);
bool EtableauProofSearchAtDepthWrapper_n1(TableauControl_p tableaucontrol,
                                         TableauStack_p distinct_tableaux_stack,
                                         ClauseSet_p active,
                                         ClauseSet_p extension_candidates,
                                         int max_depth,
                                         TableauStack_p new_tableaux);
ClauseTableau_p EtableauGetNextTableau(TableauStack_p distinct_tableaux_stack,
                                       PStackPointer *current_index_p);
#endif
