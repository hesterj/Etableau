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
#include <extension.h>
#include <math.h>
#include <sys/sysinfo.h>

WFormula_p ProofStateGetConjecture(ProofState_p state);

bool TFormulasShareVariables(Sig_p sig, TFormula_p a, TFormula_p b);
long ClauseSetMoveUnits(ClauseSet_p set, ClauseSet_p units);
long ClauseSetCopyUnits(TB_p bank, ClauseSet_p set, ClauseSet_p units);
long ClauseSetFreeUnits(ClauseSet_p set);

int Etableau(TableauControl_p tableaucontrol, 
									ProofState_p proofstate, 
									ProofControl_p proofcontrol, 
									TB_p bank, ClauseSet_p active, 
									int max_depth, 
									int tableauequality);
ClauseTableau_p ConnectionTableauProofSearchAtDepth(TableauControl_p tableaucontrol,
																	 ProofState_p proofstate, 
																	 ProofControl_p proofcontrol, 
																	 TableauSet_p distinct_tableaux_set,
																	 ClauseSet_p extension_candidates,
																	 int max_depth,
																	 TableauStack_p new_tableaux);
ClauseTableau_p ConnectionTableauProofSearchPopulate(TableauControl_p tableaucontrol,
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
ClauseTableau_p EtableauHailMary(TableauControl_p tableaucontrol);
void EtableauStatusReport(TableauControl_p tableaucontrol, ClauseSet_p active, ClauseTableau_p resulting_tab);
ClauseSet_p EtableauGetStartRuleCandidates(ProofState_p proofstate, ClauseSet_p active);
TableauSet_p EtableauCreateStartRules(ProofState_p proofstate, 
												  ProofControl_p proofcontrol, 
												  TB_p bank, 
												  FunCode max_var,
												  ClauseSet_p unit_axioms,
												  ClauseSet_p start_rule_candidates);
    

#endif
