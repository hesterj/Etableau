#ifndef ETABLEAUHASH
#define ETABLEAUHASH
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
    ET_INTEGER,
    ET_TABLEAU
} EntryType;

typedef ENTRY* Entry_p;
#define ETABLEAU_HASH_SIZE 8192

typedef struct etableauhash
{
    long size;
    struct hsearch_data *hstruct;
    PStack_p entries;
    EntryType entrytype;
}EtableauHashCell, *EtableauHash_p;

#define EtableauHashCellAlloc() (EtableauHashCell*)SizeMalloc(sizeof(EtableauHashCell))
#define EtableauHashCellFree(junk) SizeFree(junk, sizeof(EtableauHashCell))
EtableauHash_p EtableauHashAlloc(long size);
void EtableauHashFree(EtableauHash_p trash);
long EtableauHashGrow(EtableauHash_p handle);

Entry_p EntryAlloc(char* key, void* data);
void EntryFree(Entry_p trash);

#endif
