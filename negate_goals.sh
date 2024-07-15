#!/bin/bash

rm ./negated_goals/*.pog

for original in ../zenodo-dataset-pog-20220905/*/*.pog
do
    out=${original#*20220905/}
    out=${out////-}
    ./bench_sat -i $original -o "./negated_goals/${out}"
done
