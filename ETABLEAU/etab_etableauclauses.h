#ifndef ETABLEAUCLAUSES
#define ETABLEAUCLAUSES

#include <clb_os_wrapper.h>
#include <cio_signals.h>
#include <ccl_fcvindexing.h>
#include <che_heuristics.h>
#include <che_axiomscan.h>
#include <che_to_autoselect.h>
#include <cco_clausesplitting.h>
#include <cco_forward_contraction.h>
#include <cco_interpreted.h>
#include <ccl_satinterface.h>
#include <cco_proofproc.h>
#include <cco_scheduling.h>
#include <cco_proc_ctrl.h>
#include <etab_apr.h>
#include <time.h>
#include <arpa/inet.h>
#include <clb_plist.h>
#include <clb_quadtrees.h>
#include <clb_objtrees.h>

#define _GNU_SOURCE
#include <search.h>

#ifdef ETAB_IMPROVEDCOPY
#define EtableauClauseCopy(clause, branch_variables, tableau_variables) \
    EtableauClauseCopyReal(clause, branch_variables, tableau_variables)
#define EtableauClauseCopy(set, branch_variables, tableau_variables) \
    EtableauClauseSetCopyReal(set, branch_variables, tableau_variables)
#else
#define EtableauClauseCopy(clause, branch_variables, tableau_variables) ClauseCopyOpt(clause)
#define EtableauClauseSetCopy(set, branch_Variables, tableau_variables) ClauseSetCopyOpt(set)
#endif

Clause_p EtableauClauseCopyReal(Clause_p clause, PDArray_p branch_variables, PDArray_p tableau_variables);
ClauseSet_p EtableauClauseSetCopyReal(ClauseSet_p clause, PDArray_p branch_variables, PDArray_p tableau_variables);

ClauseSet_p ClauseSetCopy(TB_p bank, ClauseSet_p set);
ClauseSet_p ClauseSetCopyOpt(ClauseSet_p set);
ClauseSet_p ClauseSetCopyDisjoint(TB_p bank, ClauseSet_p set);
ClauseSet_p ClauseSetFlatCopy(ClauseSet_p set);

//typedef enum
//{
    //ETCIgnoreProps = 0,
    //ETCOriginalReference = 1,
    //ETCSharedReference = 2*ETCOriginalReference,
//}EtableauClauseProperties;
//
//typedef struct etableauclausecell
//{
    //EtableauClauseProperties properties;
    //Clause_p clause;
//}EtableauClauseCell, *EtableauClause_p;
//
//#define EtableauClauseCellAlloc() (EtableauClauseCell*) SizeMalloc(sizeof(EtableauClauseCell))
//#define EtableauClauseCellFree(junk) SizeFree(junk, sizeof(EtableauClauseCell))
//#define EtableauClauseSetProp(clause, prop) SetProp((clause), (prop))
//#define EtableauClauseDelProp(clause, prop) DelProp((clause), (prop))
//#define EtablaeuClauseGiveProps(clause, prop) GiveProps((clause), (prop))
//#define EtableauCLauseQueryProp(clause, prop) QueryProp((clause), (prop))
//
//EtableauClause_p EtableauClauseAlloc(Clause_p clause);

#endif
