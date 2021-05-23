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

typedef enum
{
    ETCIgnoreProps = 0,
    ETCOriginalReference = 1,
    ETCSharedReference = 2*ETCOriginalReference,
}EtableauClauseProperties;

typedef struct etableauclausecell
{
    EtableauClauseProperties etc_properties;
    Clause_p clause;
}EtableauClauseCell, *EtableauClause_p;
#endif
