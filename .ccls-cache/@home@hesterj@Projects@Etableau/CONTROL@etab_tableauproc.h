/*-----------------------------------------------------------------------

  File  : tableauproc.h

  Author: John Hester (hesterj@ufl.edu)

  Contents

  Main proof procedure for Etableau.  

  Copyright 2010-1019 by the author.
  This code is released under the GNU General Public Licence and
  the GNU Lesser General Public License.
  See the file COPYING in the main E directory for details..
  Run "eprover -h" for contact information.

  -----------------------------------------------------------------------*/

#ifndef TABLEAUSATURATE

#define TABLEAUSATURATE

//#include <etableau.h>
#include <etab_extension.h>
#include <math.h>
#include <sys/sysinfo.h>
#include <etab_apr.h>

WFormula_p ProofStateGetConjecture(ProofState_p state);

bool TFormulasShareVariables(Sig_p sig, TFormula_p a, TFormula_p b);
long ClauseSetMoveUnits(ClauseSet_p set, ClauseSet_p units);
long ClauseSetCopyUnits(TB_p bank, ClauseSet_p set, ClauseSet_p units);
long ClauseSetFreeUnits(ClauseSet_p set);
bool EtableauWait(int num_cores_available, EPCtrlSet_p process_set);
int TableauControlGetCores(TableauControl_p tableaucontrol);

int Etableau(TableauControl_p tableaucontrol,
						 ProofState_p proofstate,
						 ProofControl_p proofcontrol,
             TB_p bank,
             ClauseSet_p active,
             int max_depth,
             int tableauequality);
bool EtableauProofSearch(TableauControl_p tableaucontrol,
									  ProofState_p proofstate,
									  ProofControl_p proofcontrol,
									  TableauSet_p distinct_tableaux_set,
									  ClauseSet_p extension_candidates,
									  ClauseSet_p active,
									  int starting_depth,
									  int max_depth,
									  PStack_p new_tableaux);
bool EtableauMultiprocess(TableauControl_p tableaucontrol,
                          ProofState_p proofstate,
                          ProofControl_p proofcontrol,
                          TableauSet_p distinct_tableaux_set,
                          ClauseSet_p extension_candidates,
                          ClauseSet_p active,
                          int starting_depth,
                          int max_depth,
                          PStack_p new_tableaux);
ClauseTableau_p ConnectionTableauProofSearchAtDepth(TableauControl_p tableaucontrol,
                                                    ProofState_p proofstate, 
                                                    ProofControl_p proofcontrol, 
                                                    TableauSet_p distinct_tableaux_set,
                                                    ClauseSet_p extension_candidates,
                                                    int max_depth,
                                                    TableauStack_p new_tableaux,
                                                    int desired_num_tableaux);
ClauseTableau_p ConnectionCalculusExtendOpenBranches(ClauseTableau_p active_tableau, 
                                                     TableauStack_p new_tableaux,
                                                     TableauControl_p control,
                                                     TableauSet_p distinct_tableaux,
                                                     ClauseSet_p extension_candidates,
                                                     int max_depth, 
                                                     TableauStack_p max_depth_tableaux);
ClauseTableau_p ConnectionCalculusExtendSelectedBranch(ClauseTableau_p active_tableau, 
                                                       TableauStack_p newly_created_tableaux,
                                                       TableauControl_p tableaucontrol,
                                                       TableauSet_p distinct_tableaux,
                                                       ClauseSet_p extension_candidates,
                                                       int max_depth, 
                                                       TableauStack_p max_depth_tableaux);
ClauseTableau_p EtableauHailMary(TableauControl_p tableaucontrol);
ClauseSet_p EtableauGetStartRuleCandidates(ProofState_p proofstate,
                                           ClauseSet_p active);
TableauSet_p EtableauCreateStartRules(ProofState_p proofstate, 
                                      ProofControl_p proofcontrol, 
                                      TB_p bank, 
                                      FunCode max_var,
                                      ClauseSet_p unit_axioms,
                                      ClauseSet_p start_rule_candidates,
                                      TableauControl_p tableaucontrol);
TableauStack_p EtableauCreateStartRulesStack(ProofState_p proofstate,
                                      ProofControl_p proofcontrol,
                                      TB_p bank,
                                      FunCode max_var,
                                      ClauseSet_p unit_axioms,
                                      ClauseSet_p start_rule_candidates,
                                      TableauControl_p tableaucontrol);

ClauseTableau_p tableau_select(TableauControl_p tableaucontrol, TableauSet_p set);
ClauseTableau_p branch_select(TableauSet_p open_branches, int current_depth, int max_depth, int *depth_status);
ClauseTableau_p branch_select2(TableauSet_p open_branches, int current_depth, int max_depth, int *depth_status);

#endif
