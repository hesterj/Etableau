Install instructions:

```
./configure
make rebuild
cd PROVER
./eprover -h | 
```

Etableau is installed and licensed in the same way as Eprover.  Usage is also the same, except with some options added.  Try Etableau proof seach with:

```
./eprover --auto -s --tableau=1 --tableau-depth=10 SET114-6.p
```

If a successful proof (closed tableau) is not found up to tableau depth, search will abort.  If the option --tableau is not set to 1, Eprover will operate normally.
