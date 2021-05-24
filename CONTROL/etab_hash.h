#ifndef ETABLEAUHASH
#define ETABLEAUHASH

#include"etab_etableauclauses.h"

typedef enum
{
    ET_INTEGER,
    ET_TABLEAU
} EntryType;

//typedef ENTRY* Entry_p;
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

//Entry_p EntryAlloc(char* key, void* data);
//void EntryFree(Entry_p trash);

#endif
