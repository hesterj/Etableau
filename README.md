
Etableau
========

Etableau is a first order theorem prover for first order logic based 
on Eprover, using it as a library.  Etableau combines the superposition
calculus and the clausal tableaux calculus in a novel way, using the
tableaux calculus to generate lemmas and new assumptions that can be 
used to find contradictions in certain situations.

This means that branches of a tableau that are difficult to close using
the clausal tableau calculus can be closed with Eprover's saturation.
The saturation procedure benefits from the extra assumptions that are 
present on the branch of the tableau.  It seems that saturation procedures
often find a proof quickly or not at all, so by doing many short proof
searches with differing assumptions it is possible for proofs to be found
that may not have been otherwise.

Etableau is licensed and installed in the same way as Eprover.

To install Etableau, clone this repository, execute the following commands,
or follow the instructions for Eprover.

``` 
    ./configure
    make rebuild
```
    
The executable "eprover" is generated in the PROVER directory.  To check that it worked,
try running ./eprover --tableau=1 --tableau-depth=10 $1, where $1 is some TPTP problem file.

tableau
---------
--tableau=1 enables clausal tableaux proof search.  If this option is not passed, normal
Eprover will happen.

tableau-saturation
--------------------

--tableau-saturation=1 enables the combination of the superposition calculus and tableaux
calculus.

tableau-dor-print
-------------------
--tableau-dot-print=dir prints DOT graphs of the closed tableau found in a successful proof 
search to the directory dir.

apr
-----
--apr=3 filters the axiom specification to only include clauses within an alternating
path relevance distance of 3 from the conjectures of the specification.  This number can 
be changed.  This option is not recommended except on the largest problems.

quicksat
----------
--quicksat=100 ensures that no more than 100 clauses are processed during saturation of
tableau branches.  This number can be changed.  The default value is 100 if the option
--quicksat is passed without an integer option.  If quicksat is passed, then there will
be a loss of completeness for branch saturations, but not the entire proof search.  This
is becuase of the fact that if only a small number of clauses are going to be processed
on a branch saturation, there is no need to copy the entire unprocessed clause set and
only a small number or none are copied.

tableau-equality
------------------
--tableau-equality=1 introduces equality axioms for the symbols found in the specification
as well as axioms of symmetry, reflection, and transitivity.  This is helpful on some
problems.  This is not normally necessary because if equality is detected in the signature
of a problem, equality axioms are automatically added.

Eprover options
---------------
Options controlling the saturation procedure of Eprover also work, allowing the user 
to use different strategies.

Help
----

If you have any problems with this software or a bug report, please feel free to contact
me at hesterj@ufl.edu.


