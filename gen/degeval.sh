#!/bin/bash
# skriv ut dmax för fall $1
N=$1
cat > /root/lr/DegEval$N.lean <<EOT
import LeanResidy.Points
import LeanResidy.Data$N
namespace LeanResidy.C$N
def DT : LP := trL t00 t01 t10 t11 D
def pfin (k l : ℕ) := PFfinL.getD (k * V + l) []
def pinf (k l : ℕ) := PFinfL.getD (k * V + l) []
def iz : ℕ := pts.length - 1
def entryS (k l : ℕ) : List (Mon K) :=
  smul (slev (A k l) (spar ex1) (spar (ex1.map (- ·))) (spar ex2) (spar (ex2.map (- ·)))) (sdlog ev1) ++
  sneg (smul (slev (eul DT) (spar ev1) (spar (ev1.map (- ·))) (spar ev2) (spar (ev2.map (- ·))))
    (spf iz (pfin k l) (pinf k l)))
#eval ((List.range V).flatMap fun k => (List.range V).map fun l => sdeg pts.length (entryS k l) (kvecs (entryS k l))).foldr max 0
end LeanResidy.C$N
EOT
cd /root/lr && lake build LeanResidy.Data$N 2>&1 | grep -i error; lake env lean DegEval$N.lean
