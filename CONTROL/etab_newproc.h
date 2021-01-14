#ifndef ETAB_NEWPROC
#define ETAB_NEWPROC
#include<etab_tableauproc.h>


int Etableau_n(TableauControl_p tableaucontrol,
               ProofState_p proofstate,
               ProofControl_p proofcontrol,
               TB_p bank,
               ClauseSet_p active,
               int max_depth,
               int tableauequality);

ClauseTableau_p EtableauProofSearch_n(TableauControl_p tableaucontrol,
                                      ClauseTableau_p state,
                                      ClauseSet_p extension_candidates,
                                      int current_depth,
                                      int max_depth,
                                      BacktrackStatus_p backtrack_status);
bool EtableauMultiprocess_n(TableauControl_p tableaucontrol,
                            PStack_p starting_tableaux,
                            ClauseSet_p extension_candidates,
                            int max_depth);
ClauseTableau_p EtableauProofSearchAtDepth_n(TableauControl_p tableaucontrol,
                                             ClauseTableau_p master,
                                             ClauseSet_p extension_candidates,
                                             int max_depth,
                                             BacktrackStatus_p status);
bool EtableauProofSearchAtDepthWrapper_n(TableauControl_p tableaucontrol,
                                         TableauStack_p distinct_tableaux_stack,
                                         ClauseSet_p active,
                                         ClauseSet_p extension_candidates,
                                         int max_depth);
ClauseTableau_p EtableauGetNextTableau(TableauStack_p distinct_tableaux_stack,
                                       PStackPointer *current_index_p);
#endif
