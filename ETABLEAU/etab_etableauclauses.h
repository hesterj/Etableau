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
#define EtableauClauseCopy(clause, bank, array) EtableauClauseCopy(clause, array)
#else
#define EtableauClauseCopy(clause, bank, array) ClauseCopyOpt(clause)
#endif

typedef enum
{
    ETCIgnoreProps = 0,
    ETCOriginalReference = 1,
    ETCSharedReference = 2*ETCOriginalReference,
}EtableauClauseProperties;

typedef struct etableauclausecell
{
    EtableauClauseProperties properties;
    Clause_p clause;
}EtableauClauseCell, *EtableauClause_p;

#define EtableauClauseCellAlloc() (EtableauClauseCell*) SizeMalloc(sizeof(EtableauClauseCell))
#define EtableauClauseCellFree(junk) SizeFree(junk, sizeof(EtableauClauseCell))
#define EtableauClauseSetProp(clause, prop) SetProp((clause), (prop))
#define EtableauClauseDelProp(clause, prop) DelProp((clause), (prop))
#define EtablaeuClauseGiveProps(clause, prop) GiveProps((clause), (prop))
#define EtableauCLauseQueryProp(clause, prop) QueryProp((clause), (prop))

EtableauClause_p EtableauClauseAlloc(Clause_p clause);

#endif
