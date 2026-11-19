#!/bin/sh
# build_parts.sh N [K I]
# build_parts.sh N -f LIST
#
# Builds the evaluated modules of Cert/ (the files Cert/<search>/M<k>.lean) N at a time: each call of
# `lake build` gets N modules and Lake runs those N in parallel, then the next N follow. Lake on its own starts
# every module that is ready, so a plain `lake build AlmanacSolution` would start thousands of Lean processes.
#
# With K and I, only every K-th module from the I-th on (I = 0 .. K-1) is built, so K machines can share the run.
# With -f LIST, only the modules named in the file LIST (a path from this directory) are built, one per line,
# as `Cert.F0.M12`; the file .parts.txt that a run writes is such a list. See README.md for putting the results
# together. A run that is stopped can be started again: Lake keeps the modules that are done.
#
# Memory: one Lean process needs 1.5 to 6 GB, so N should be at most the free memory divided by 6 GB.
N=${1:-4}
cd "$(dirname "$0")" || exit 1
if [ "$2" = "-f" ]; then
  sed 's/\r$//' "$3" | grep . > .parts.new && mv .parts.new .parts.txt
else
  K=${2:-1}
  I=${3:-0}
  find Cert -name 'M*.lean' | sort | awk -v k="$K" -v i="$I" '(NR - 1) % k == i' \
    | sed 's/\.lean$//; s#/#.#g' > .parts.txt
fi
echo "$(wc -l < .parts.txt) modules, $N at a time"
xargs -n "$N" lake build < .parts.txt
