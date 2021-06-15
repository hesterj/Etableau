#------------------------------------------------------------------------
#
# File  : Makefile for ETABLEAU part of thew CLIB library/E Prover
#
# John Hester added this
#
# Changes
#
# <1> Mon Jun  8 11:09:27 MET DST 1998
#     New
#
#------------------------------------------------------------------------

include ../Makefile.vars

# Project specific variables

PROJECT = ETABLEAU
LIB     = $(PROJECT).a

all: $(LIB)

depend: *.c *.h
	$(MAKEDEPEND)

# Remove all automatically generated files

clean:
	@touch does_exist.o does_exist.a; rm *.o  *.a

# Services (provided by the master Makefile)

include ../Makefile.services

ETABLEAU_LIB =  etab_extension.o etab_clausetableaux.o\
				etab_tableauproc.o etab_foldingup.o \
				etab_localunification.o etab_closure.o \
				etab_etableau.o	etab_apr.o \
				etab_xgboost_interaction.o etab_backtrack.o \
				etab_newproc.o etab_hash.o\
				etab_etableauclauses.o\

$(LIB): $(ETABLEAU_LIB)
	$(AR) $(LIB) $(ETABLEAU_LIB)

include Makefile.dependencies

