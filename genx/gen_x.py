"""Genererar en datafil för LeanResidy.X (Case K) ur run.main i en KOPIA av residymetod_nya_fall/kod.
Kör: BRDIR=<kopia>/kod python3 gen_x.py f2a   (skriver ~/lr/LeanResidy/X/Data<namn>.lean)"""
import sys, os, time, pickle
BR = os.environ['BRDIR']
sys.path.insert(0, BR)
sys.dont_write_bytecode = True
os.chdir(BR)
from flint import fmpq
import run as RUN
import nyfall
RUN.setup = nyfall.setup
name = sys.argv[1]
t0 = time.time()
F, P, D, A, loc, T, b0 = RUN.main(name)
F_, Px, Fc, _, _ = nyfall.setup(name)
D0, A0 = pickle.load(open(f'{BR}/symb_x_{name}.pkl', 'rb'))

def q(x):
    x = fmpq(x); p, d = int(x.p), int(x.q)
    return f"({p} : ℚ)" if d == 1 else f"({p}/{d} : ℚ)"

assert F.n == 3
KT = f"Z8 ({F.gens[0]}) ({F.gens[1]}) ({q(F.gens[2])})"
def kq(x):           # rationellt tal som element i K
    return kel(F(x))
def kel(k):
    c = k.c
    z4 = lambda a: "⟨" + ", ".join(q(v) for v in a) + "⟩"
    return f"(⟨{z4(c[0:4])}, {z4(c[4:8])}⟩ : K)"
def lp(d):
    return "[" + ", ".join(f"(({a}, {b}), {kq(c)})" for (a, b), c in sorted(d.items())) + "]"
def edges(ed):
    return "[" + ", ".join(f"({i}, {j}, {n1}, {n2}, {kq(w)})" for i, j, (n1, n2), w in ed) + "]"

keys = list(P.pts.keys())
zero_key = F(0).key()
keys = [k for k in keys if k != zero_key] + [zero_key]
def pp(s, qk):
    out = []
    top = 1 if qk == 'inf' else 0
    for k in range(s.v, top):
        c = s.coef(k)
        if not c.is_zero(): out.append((-k, c))
    return out
PF = {}
for kl, d in A.items():
    if d: PF[kl] = {qk: pp(loc[qk][2][kl], qk) for qk in loc}
V = Fc[0]
idx = {k: i for i, k in enumerate(keys)}
ex = lambda Pp, k: "[" + ", ".join(str(Pp.E[k].get(kk, 0)) for kk in keys) + "]"
assert all(c == F(1) for c in Px.c) and all(c == F(1) for c in P.c)
fin_all, inf_all = [], []
for i in range(V):
    for j in range(V):
        if (i, j) not in PF:
            fin_all.append("[]"); inf_all.append("[]"); continue
        fin, inf = [], []
        for qk, lst in PF[(i, j)].items():
            for m, c in lst:
                if qk == 'inf': inf.append(f"({m}, {kel(c)})")
                else: fin.append(f"({idx[qk]}, {m}, {kel(c)})")
        fin_all.append("[" + ", ".join(fin) + "]"); inf_all.append("[" + ", ".join(inf) + "]")
ns = 'C' + name
L = [f"import LeanResidy.X.Case\n",
     f"/-! Genererad av genx/gen_x.py {name} ur en kopia av residymetod_nya_fall/kod (run.main). -/\n",
     "namespace LeanResidy.X", f"namespace {ns}\n",
     f"abbrev K := {KT}\n",
     "def data : Case K where",
     f"  V := {V}",
     f"  E := {edges(Fc[1])}",
     f"  AL := [" + ",\n    ".join(lp(A0.get((i, j), {})) for i in range(V) for j in range(V)) + "]",
     f"  D := {lp(D0)}",
     "  pts := [" + ", ".join(kel(P.pts[k]) for k in keys) + "]",
     f"  ex1 := {ex(Px, 0)}", f"  ex2 := {ex(Px, 1)}",
     f"  t00 := {T[0][0]}", f"  t01 := {T[0][1]}", f"  t10 := {T[1][0]}", f"  t11 := {T[1][1]}",
     f"  ev1 := {ex(P, 0)}", f"  ev2 := {ex(P, 1)}",
     "  PFfinL := [" + ",\n    ".join(fin_all) + "]",
     "  PFinfL := [" + ",\n    ".join(inf_all) + "]",
     f"  dmax := DMAX\n",
     f"end {ns}", "end LeanResidy.X\n"]
open(os.path.expanduser(f'~/lr/LeanResidy/X/Data{name}.lean'), 'w').write("\n".join(L))
print('klart', time.time() - t0, file=sys.stderr)
