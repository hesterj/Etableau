#!/bin/sh

# Delete this if only missing problems are added!
# cat /dev/null > ../problem_features_7.2.0_raw

for file in `ls|grep [_+=-].*\.p`; do
#for file in `gawk '/^[^#]/{print $1}' ../missing`; do
    echo "Processing " $file
    ProblemSPC=`grep " SPC " $file | sed -e "s/.* : //"`
    # echo $ProblemSPC
    if  [ `expr "$ProblemSPC" : "TF0.*"` != 0 ]  || [ `expr "$ProblemSPC" : "FOF.*"` != 0 ] || [ `expr "$ProblemSPC" : "CNF.*"` != 0 ]  ; then
       # echo $file
       ulimit -t 5000
       classify_problem --free-numbers --sine=Auto --no-preprocessing $file>> ../problem_features_7.3.0_nopraw
    else
           echo "Skipping " $file
    fi
done
