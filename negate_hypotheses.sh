#!/bin/bash

rm ./negated_hypotheses/*.pog

for original in ../zenodo-dataset-pog-20220905/*/*.pog
do
    out=${original#*20220905/}
    out=${out////-}
    ./bench_sat -i $original -o "./negated_hypotheses/${out}" -h -c 3 -n 0.33
done
