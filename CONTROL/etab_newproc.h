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

#endif
