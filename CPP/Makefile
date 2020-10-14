#------------------------------------------------------------------------
#
# File  : Makefile for CPP.a library of generic data types and
# algorithms.
#
# Author: Stephan Schulz
#
# Created: Sun Jul  6 22:55:11 MET DST 1997
#
#------------------------------------------------------------------------

include ../Makefile.vars

# Project specific variables

PROJECT = CPP
LIB     = $(PROJECT).a

all: $(LIB)

cppdepend: *.cpp *.h
	echo 'About to compile C++ interface...'
	$(CXX) -M -O3 -I../include *.cpp > Makefile.dependencies;

depend: *.cpp *.h
	$(info $(MAKEDEPENDPP))
	$(MAKEDEPENDPP)

# Remove all automatically generated files

clean:
	@rm -f *.o  *.a

# Services (provided by the master Makefile)

include ../Makefile.services

# Build the  library

CPP_LIB = cpp_interface.o
$(LIB): $(CPP_LIB)
	$(info Executing $(AR) $(LIB) $(CPP_LIB))
	$(AR) $(LIB) $(CPP_LIB)
include Makefile.dependencies
