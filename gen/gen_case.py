import sys, time, json
from gen_common import *
import run as RUN
if '/nya' in BR:
    import nyfall as _nf
    RUN.setup = _nf.setup
from flint import fmpq
name = sys.argv[1]
t0=time.time()
F, P, D, A, loc, T, b0 = RUN.main(name)
if '/nya' in BR:
    import nyfall
    F_, Px, Fc, _, _ = nyfall.setup(name)
else:
    import cases
    if name in ('346','4612'):
        F_, Px, Fc = cases.tri_param(name)
    else:
        F_, Px, Fc = cases.f3_param()
D0, A0 = pickle.load(open(f'{BR}/symb_x_{name}.pkl','rb'))
# punkt-lista: alla punkter i P.pts (inkl. 0 som run.main lagt till sist)
keys = list(P.pts.keys())
zero_key = F(0).key()
keys = [k for k in keys if k != zero_key] + [zero_key]
def pp(s, qk):
    out = []
    if qk == 'inf':
        for k in range(s.v, 1):
            c = s.coef(k)
            if not c.is_zero(): out.append((-k, c))
    else:
        for k in range(s.v, 0):
            c = s.coef(k)
            if not c.is_zero(): out.append((-k, c))
    return out
PF = {}
for kl, d in A.items():
    if not d: continue
    PF[kl] = {qk: pp(loc[qk][2][kl], qk) for qk in loc}
AB = (F.A, F.B)
V = Fc[0]
L = []
L.append("import LeanResidy.Lap\n")
L.append(f"/-! Genererad av gen/gen_case.py {name} ur {BR} (run.main). -/\n\nnamespace LeanResidy\n")
ns = 'C' + name
L.append(f"namespace {ns}\n")
L.append(f"abbrev KA : ℤ := {AB[0]}\nabbrev KB : ℤ := {AB[1]}\nabbrev K := Z4 KA KB\n")
L.append(f"def V : ℕ := {V}\n")
L.append(f"def E : List Edge := {edges(Fc[1])}\n")
L.append(f"def D : LP := {lp(D0)}\n")
L.append("def AL : List LP := [" + ",\n  ".join(lp(A0.get((i,j),{})) for i in range(V) for j in range(V)) + "]\n")
L.append(f"def A (i j : ℕ) : LP := AL.getD (i * V + j) []\n")
L.append("/-- punkteringarna (sista = 0) -/")
L.append("def pts : List K := [" + ", ".join(z4(P.pts[k], AB) for k in keys) + "]\n")
# exponenter i x-koordinater (Px) och v-koordinater (P)
def ex(Pp, k):
    return "[" + ", ".join(str(Pp.E[k].get(kk, 0)) for kk in keys) + "]"
assert all(c == F(1) for c in Px.c)
L.append(f"/-- x(z): exponenter per punkt -/\ndef ex1 : List ℤ := {ex(Px,0)}\ndef ex2 : List ℤ := {ex(Px,1)}\n")
print('P.c', [str(c) for c in P.c], 'T', T, file=sys.stderr)
L.append(f"def t00 : ℤ := {T[0][0]}\ndef t01 : ℤ := {T[0][1]}\ndef t10 : ℤ := {T[1][0]}\ndef t11 : ℤ := {T[1][1]}\n")
L.append(f"/-- v(z) = x^(T⁻¹): exponenter -/\ndef ev1 : List ℤ := {ex(P,0)}\ndef ev2 : List ℤ := {ex(P,1)}\n")
Dt = tr(D0, T) if False else None
assert all(c == F(1) for c in P.c)
idx = {k: i for i, k in enumerate(keys)}
# PF per post (k, l): ändliga delar och ∞-del
fin_all = []; inf_all = []
for i in range(V):
    for j in range(V):
        if (i, j) not in PF:
            fin_all.append("[]"); inf_all.append("[]"); continue
        d = PF[(i, j)]
        fin = []; inf = []
        for qk, lst in d.items():
            if qk == 'inf':
                for m, c in lst: inf.append(f"({m}, {z4(c, AB)})")
            else:
                for m, c in lst: fin.append(f"({idx[qk]}, {m}, {z4(c, AB)})")
        fin_all.append("[" + ", ".join(fin) + "]"); inf_all.append("[" + ", ".join(inf) + "]")
L.append("/-- partialbråk för ρ_{kl}: (punktindex i, ordning m, c) betyder c/(z − ptsᵢ)^m -/")
L.append("def PFfinL : List (List (ℕ × ℕ × K)) := [" + ",\n  ".join(fin_all) + "]\n")
L.append("/-- polynomdelen: (k, c) betyder c·z^k -/")
L.append("def PFinfL : List (List (ℕ × K)) := [" + ",\n  ".join(inf_all) + "]\n")
L.append(f"end {ns}\n\nend LeanResidy\n")
open(f'/root/lr/LeanResidy/Data{name}.lean', 'w').write("\n".join(L))
print('klart', time.time()-t0, file=sys.stderr)
