#!/bin/bash
# skriv ut dmax för X-fallet $1 (datafilen måste ha dmax := DMAX ersatt med ett tal först)
N=$1
sed -i 's/dmax := DMAX/dmax := 0/' ~/lr/LeanResidy/X/Data$N.lean
cat > ~/lr/DegEvalX$N.lean <<EOT
import LeanResidy.X.Data$N
open LeanResidy.X LeanResidy
#eval ((List.range C$N.data.V).flatMap fun k => (List.range C$N.data.V).map fun l => sdeg C$N.data.pts.length (C$N.data.entryS k l) (kvecs (C$N.data.entryS k l))).foldr max 0
EOT
cd ~/lr && export PATH=~/.elan/bin:$PATH && lake build LeanResidy.X.Data$N 2>&1 | grep -i "error" ; lake env lean DegEvalX$N.lean 2>&1 | grep -v "module system"
