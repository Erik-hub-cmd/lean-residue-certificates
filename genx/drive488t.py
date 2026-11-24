import sys, os, pickle
sys.path.insert(0, os.path.expanduser('~/lr/genx'))
from fractions import Fraction as Fr
from emit2 import *
from flint import fmpq
R = pickle.load(open(os.path.expanduser('~/lr/genx/raw488.pkl'), 'rb'))
ts = sorted(R); r0 = R[ts[0]]
for t in ts: assert R[t]['T'] == r0['T'] and R[t]['keys'] == r0['keys'] and R[t]['E'] == r0['E'] and R[t]['Ex'] == r0['Ex']
NPT = int(sys.argv[1])            # antal kontrollpunkter = dmax + 1
# tpts: 0, 1, −1, i, −i, sedan ±c, ±ic för c = 2..NPT+1
base = [(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)]
extra = []
for c in range(2, NPT + 2): extra += [(c, 0), (-c, 0), (0, c), (0, -c)]
tp = base + extra
tptsL = "[" + ", ".join(f"(⟨{q(a)}, {q(b)}, 0, 0⟩ : Z4 (-1) (-2))" for a, b in tp) + "]"
def den(t, k):
    a, b, c, d = k[:4] + [0] * (4 - len(k[:4])) if len(k) >= 4 else (k + [0] * 4)[:4]
    e = k[4] if len(k) > 4 else 0
    assert d == e
    return t ** a * (t - 1) ** b * (t + 1) ** c * (t * t + 1) ** d
fit = Fit(ts, den, 14)
cv = lambda x: Fr(int(fmpq(x).p), int(fmpq(x).q))
kDA = [4]
Dfit = lp_fit(fit, [{k: cv(v) for k, v in R[t]['D'].items()} for t in ts], kDA)
V = 4
Afit = [lp_fit(fit, [{k: cv(v) for k, v in R[t]['A'].get((i, j), {}).items()} for t in ts], kDA) for i in range(V) for j in range(V)]
keys = r0['keys']; idx = {k: n for n, k in enumerate(keys)}
fin_all, inf_all = pf_fit(fit, R, ts, V, idx, [2, 3, 1, 1, 1])
# punkterna i z som polynom i u
val = {'1': [(1, 0)], 'u': [(0, 0), (1, 0)], '-i': [(0, -1)], '-iu': [(0, 0), (0, -1)], '0': [(0, 0)]}
def ptL(lab):
    sg, nm = lab
    cs = val[nm]
    if sg == '-': cs = [(-a, -b) for a, b in cs]
    return f"(⟨[{', '.join(f'⟨{q(a)}, {q(b)}, 0, 0⟩' for a, b in cs)}], []⟩ : K)"
ptsL = "[" + ", ".join(ptL(k) for k in keys) + "]"
ex = lambda E: "[" + ", ".join(str(E.get(kk, 0)) for kk in keys) + "]"
wq = "(⟨[⟨(-1/2 : ℚ), 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨(-1/2 : ℚ), 0, 0, 0⟩], [1]⟩ : K)"   # 1 − c = −(u − 1)²/(2u)
wo = "(⟨[⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩], [1]⟩ : K)"                    # 2c = (u² + 1)/u
import lat
Vg, ed = lat.get('4.8^2', ['q', 'o'])
Ered = "[" + ", ".join(f"({i}, {j}, {n1}, {n2}, {wq if w == 'q' else wo})" for i, j, (n1, n2), w in ed) + "]"
write(os.path.expanduser('~/lr/LeanResidy/X/Data488u.lean'), '488u',
      '4.8² med vikterna (1 − c, 2c) ∝ (1, t), c = (u + 1/u)/2 = cos θ, symboliskt i u.', (-1, -2), tptsL, V, Ered,
      Afit, Dfit, ptsL, ex(r0['Ex'][0]), ex(r0['Ex'][1]), r0['T'], ex(r0['E'][0]), ex(r0['E'][1]), fin_all, inf_all)
print('ok')
