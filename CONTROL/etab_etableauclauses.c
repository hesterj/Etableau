#include"etab_etableauclauses.h"

EtableauClause_p EtableauClauseAlloc(Clause_p clause)
{
    EtableauClause_p wrapped_clause = EtableauClauseCellAlloc();
    wrapped_clause->properties = ETCIgnoreProps;
    wrapped_clause->clause = clause;
}

void EtableauClauseFree(EtableauClause_p junk)
{
    EtableauClauseCellFree(junk);
}
