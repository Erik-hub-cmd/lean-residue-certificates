"""Exakt tvåparameterdata (a = u, b = r) för [3.4.3.12; 3.12²] med alla vikter, direkt i den
Kroneckerpackade modellen. Koefficienterna interpoleras exakt på ett rutnät ur run.main (probe_f2b.py,
kopia av residymetod_nya_fall/kod) och kontrolleras i ALLA rutnätspunkter. Lean litar inte på
interpolationen: ett fel ger en misslyckad kontroll.

python3 fit2.py UT.lean NS Kb S QMAX DMAX DMAXC grid*.pkl
"""
import os, sys, pickle
from fractions import Fraction as Q
from math import lcm
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

A, B = -1, -2

def FF(z):
    if hasattr(z, 'p'): return Q(int(z.p), int(z.q))
    return Q(z)

def lagrange(xs, ys):
    n = len(xs); coef = [Q(0)] * n
    for i in range(n):
        num = [Q(1)]; den = Q(1)
        for j in range(n):
            if j == i: continue
            num = [Q(0)] + num
            for k in range(len(num) - 1): num[k] -= xs[j] * num[k + 1]
            den *= xs[i] - xs[j]
        for k in range(n): coef[k] += ys[i] * num[k] / den
    while coef and coef[-1] == 0: coef.pop()
    return coef
def peval(c, x):
    r = Q(0)
    for a in reversed(c): r = r * x + a
    return r
def fit_poly(xs, ys, maxdeg):
    c = lagrange(xs[:maxdeg + 1], ys[:maxdeg + 1])
    if all(peval(c, x) == y for x, y in zip(xs, ys)): return c
    return None

# ---- polynom i (u, r) med Z4-koefficienter: dict (i, j) -> 4-tupel ----
Z0 = (Q(0),) * 4
def zadd(x, y): return tuple(a + b for a, b in zip(x, y))
def zmul(x, y):
    return (x[0]*y[0] + A*x[1]*y[1] + B*x[2]*y[2] + A*B*x[3]*y[3],
            x[0]*y[1] + x[1]*y[0] + B*(x[2]*y[3] + x[3]*y[2]),
            x[0]*y[2] + x[2]*y[0] + A*(x[1]*y[3] + x[3]*y[1]),
            x[0]*y[3] + x[3]*y[0] + x[1]*y[2] + x[2]*y[1])
def padd(p, q):
    r = dict(p)
    for k, v in q.items():
        r[k] = zadd(r.get(k, Z0), v)
        if all(t == 0 for t in r[k]): del r[k]
    return r
def pmul(p, q):
    r = {}
    for k1, v1 in p.items():
        for k2, v2 in q.items():
            k = (k1[0] + k2[0], k1[1] + k2[1]); r[k] = zadd(r.get(k, Z0), zmul(v1, v2))
    return {k: v for k, v in r.items() if any(t != 0 for t in v)}
def ppow(p, n):
    r = {(0, 0): (Q(1), Q(0), Q(0), Q(0))}
    for _ in range(n): r = pmul(r, p)
    return r
def C(c): return (Q(c), Q(0), Q(0), Q(0))
def ev(p, u, r):
    s = Z0
    for (i, j), v in p.items(): s = zadd(s, tuple(t * u**i * r**j for t in v))
    return s

# nämnarfaktorer i u och r (rationella koefficienter)
FAC = {'u': {(1, 0): C(1)}, 'u-1': {(1, 0): C(1), (0, 0): C(-1)}, 'u+1': {(1, 0): C(1), (0, 0): C(1)},
       'u2+1': {(2, 0): C(1), (0, 0): C(1)}, 'r': {(0, 1): C(1)}, 'r+1': {(0, 1): C(1), (0, 0): C(1)}}
def fval(nm, u, r): return ev(FAC[nm], u, r)[0]

def exact_div(p, fac):
    """p / fac om exakt (polynomdivision i u eller r), annars None"""
    # dela via utvärdering: enkelt sätt — använd sympy
    import sympy as sp
    u, r = sp.symbols('u r')
    out = []
    for c in range(4):
        P = sum(sp.Rational(v[c].numerator, v[c].denominator) * u**i * r**j for (i, j), v in p.items())
        Fp = sum(sp.Rational(v[0].numerator, v[0].denominator) * u**i * r**j for (i, j), v in fac.items())
        qq, rem = sp.div(sp.Poly(P, u, r), sp.Poly(Fp, u, r))
        if not rem.is_zero: return None
        out.append(qq)
    res = {}
    for c in range(4):
        for (i, j), v in out[c].terms():
            t = list(res.get((i, j), Z0)); t[c] = Q(int(v.p), int(v.q)); res[(i, j)] = tuple(t)
    return {k: v for k, v in res.items() if any(t != 0 for t in v)}

class Fitter:
    def __init__(self, R):
        self.R = R
        self.us = sorted({u for u, r in R}); self.rs = sorted({r for u, r in R})
        assert all((u, r) in R for u in self.us for r in self.rs)
    def fit(self, get, tmpl):
        """get(rec) -> 4-tupel; tmpl dict faktor -> exponent. Returnerar (poly, den-dict)"""
        us, rs = self.us, self.rs
        du, dr = len(us) - 3, len(rs) - 3
        rows = {}
        for u in us:
            cs = []
            for c in range(4):
                ys = []
                for r in rs:
                    t = Q(1)
                    for nm, e in tmpl.items(): t *= fval(nm, u, r) ** e
                    ys.append(FF(get(self.R[(u, r)])[c]) * t)
                co = fit_poly(rs, ys, dr)
                if co is None: return None
                cs.append(co)
            rows[u] = cs
        p = {}
        nr = max(len(rows[u][c]) for u in us for c in range(4))
        for j in range(nr):
            for c in range(4):
                ys = [rows[u][c][j] if j < len(rows[u][c]) else Q(0) for u in us]
                co = fit_poly(us, ys, du)
                if co is None: return None
                for i, v in enumerate(co):
                    if v != 0:
                        t = list(p.get((i, j), Z0)); t[c] = v; p[(i, j)] = tuple(t)
        # förkorta nämnarfaktorer
        tm = dict(tmpl)
        for nm in list(tm):
            while tm[nm] > 0:
                q = exact_div(p, FAC[nm])
                if q is None: break
                p = q; tm[nm] -= 1
        return p, {k: v for k, v in tm.items() if v}

def poly_lean(p):
    d = 1
    for v in p.values():
        for u in v: d = lcm(d, u.denominator)
    terms = []
    for (i, j), v in sorted(p.items()):
        c = [int(u * d) for u in v]
        terms.append(f"(({i}, {j}), ⟨{c[0]}, {c[1]}, {c[2]}, {c[3]}⟩)")
    return f"mk [{', '.join(terms)}] {d}"

def main():
    out_path, ns, Kb, S, QMAX, DMAX, DMAXC = sys.argv[1], sys.argv[2], *map(int, sys.argv[3:8])
    R = {}
    for f in sys.argv[8:]: R.update(pickle.load(open(f, 'rb')))
    fitter = Fitter(R)
    print('rutnät', len(fitter.us), 'x', len(fitter.rs), flush=True)
    r0 = R[(fitter.us[0], fitter.rs[0])]
    for k, r in R.items():
        assert r['T'] == r0['T'] and r['keys'] == r0['keys'] and r['E'] == r0['E'] and r['Ex'] == r0['Ex'], k
    Dl = []; Dkey = {}
    def dl(poly, name):
        key = tuple(sorted(poly.items()))
        if key not in Dkey: Dkey[key] = len(Dl); Dl.append((poly, name))
        return Dkey[key]
    for nm in FAC: dl(FAC[nm], nm)
    def K(p, den):
        dv = {}
        for nm, e in den.items(): dv[Dkey[tuple(sorted(FAC[nm].items()))]] = e
        kv = "[" + ", ".join(str(dv.get(i, 0)) for i in range(max(dv.keys(), default=-1) + 1)) + "]"
        return f"(⟨{poly_lean(p)}, {kv}⟩ : K)"
    TA = {'u': 6}
    TP = {'u': 2, 'u-1': 2, 'u+1': 2, 'u2+1': 2, 'r': 2, 'r+1': 3}
    def fitK(get, tm):
        res = fitter.fit(get, tm)
        if res is None: raise SystemExit(f'interpolationen misslyckades med mall {tm}')
        return K(*res)
    V = 8
    D = sorted(r0['D'])
    Dl_ = "[" + ", ".join(f"(({m[0]}, {m[1]}), {fitK(lambda r, m=m: (r['D'].get(m, 0), 0, 0, 0), TA)})" for m in D) + "]"
    print('D klar', flush=True)
    AL = []
    for i in range(V):
        for j in range(V):
            mons = set()
            for r in R.values(): mons |= set(r['A'].get((i, j), {}))
            AL.append("[" + ", ".join(f"(({m[0]}, {m[1]}), {fitK(lambda r, m=m, i=i, j=j: (r['A'].get((i, j), {}).get(m, 0), 0, 0, 0), TA)})" for m in sorted(mons)) + "]")
    print('A klar', flush=True)
    keys = r0['keys']; idx = {k: n for n, k in enumerate(keys)}
    fins, infs = [], []
    for i in range(V):
        for j in range(V):
            ks = set()
            for r in R.values(): ks |= set(r['PF'].get((i, j), {}))
            fin, inf = [], []
            for (qk, m) in sorted(ks, key=lambda x: (str(x[0]), x[1])):
                el = fitK(lambda r, i=i, j=j, qk=qk, m=m: r['PF'].get((i, j), {}).get((qk, m), (0, 0, 0, 0)), TP)
                if qk == 'inf': inf.append(f"({m}, {el})")
                else: fin.append(f"({idx[qk]}, {m}, {el})")
            fins.append("[" + ", ".join(fin) + "]"); infs.append("[" + ", ".join(inf) + "]")
        print('PF rad', i, flush=True)
    # vikter: c = (u + 1/u)/2; WW = [2c(1+r), 2c r(1+r), r(1 − c(1+r))]
    u2p1 = FAC['u2+1']; rp1 = FAC['r+1']; rr = FAC['r']
    W = [K(pmul(u2p1, rp1), {'u': 1}),
         K(pmul(pmul(u2p1, rr), rp1), {'u': 1}),
         K({k: tuple(t / 2 for t in v) for k, v in pmul(rr, padd({(1, 0): C(2)}, {k: tuple(-t for t in v) for k, v in pmul(u2p1, rp1).items()})).items()}, {'u': 1})]
    sys.path.insert(0, os.environ.get('RESIDY_DIR', '.'))  # katalogen med lat.py, nyfall.py
    import lat, nyfall
    Vg, ed = lat.get(nyfall.NAMES['f2b'], [0, 1, 2]); assert Vg == V
    E = "[" + ", ".join(f"({i}, {j}, {n1}, {n2}, {W[w]})" for i, j, (n1, n2), w in ed) + "]"
    # punkteringar: ('±', lab) -> ±värde, lab ∈ 1, u, -i, -iu
    base = {'1': {(0, 0): C(1)}, 'u': {(1, 0): C(1)}, '-i': {(0, 0): (Q(0), Q(-1), Q(0), Q(0))},
            '-iu': {(1, 0): (Q(0), Q(-1), Q(0), Q(0))}}
    ptsP = []
    for sg, nm in keys:
        if nm == '0': ptsP.append({}); continue
        s = -1 if sg == '-' else 1
        ptsP.append({k: tuple(s * t for t in v) for k, v in base[nm].items()})
    for p in ptsP:
        if not any(k != (0, 0) for k in p): continue
        for q in range(2, QMAX + 1):
            dl(padd({(0, 0): C(q)}, {k: tuple(-t for t in v) for k, v in p.items()}), f"{q}-pt")
    ex = lambda Ed: "[" + ", ".join(str(Ed.get(kk, 0)) for kk in keys) + "]"
    T = r0['T']
    def plain(p): return f"(⟨{poly_lean(p)}, []⟩ : K)"
    L = ["import LeanResidy.X.Case\nimport LeanResidy.X.FrG\n",
         "/-! Genererad av genk/fit2.py. [3.4.3.12; 3.12²] med alla vikter, symboliskt i a = u, b = r\n"
         "(vikter 2c(1+r), 2cr(1+r), r(1 − c(1+r)), c = (u + 1/u)/2, som i probe_f2b.py), i den\n"
         "Kroneckerpackade modellen. Koefficienterna är exakt interpolerade på ett rutnät ur run.main;\n"
         "Lean kontrollerar identiteterna själv. -/\n",
         "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n",
         f"namespace LeanResidy.X\nnamespace {ns}\n",
         f"abbrev PKf := PK ({A}) ({B}) {Kb} {S}",
         "/-- ett data-element `P / den` -/\nabbrev mk (P : GP) (den : ℕ) : PKf := PK.ofList' P den\n",
         "/-- nämnarfaktorerna -/\ndef Dl : List PKf := [" + ",\n  ".join(poly_lean(p) for p, nm in Dl) + "]\n",
         "/-- vad faktorerna är (kommentar): " + "; ".join(f"{i}: {nm}" for i, (p, nm) in enumerate(Dl)) + " -/\n",
         "abbrev K := FrG PKf Dl\n",
         "def data : Case K where", f"  V := {V}", f"  E := {E}",
         "  AL := [" + ",\n    ".join(AL) + "]", f"  D := {Dl_}",
         "  pts := [" + ", ".join(plain(p) for p in ptsP) + "]",
         f"  ex1 := {ex(r0['Ex'][0])}", f"  ex2 := {ex(r0['Ex'][1])}",
         f"  t00 := {T[0][0]}", f"  t01 := {T[0][1]}", f"  t10 := {T[1][0]}", f"  t11 := {T[1][1]}",
         f"  ev1 := {ex(r0['E'][0])}", f"  ev2 := {ex(r0['E'][1])}",
         "  PFfinL := [" + ",\n    ".join(fins) + "]", "  PFinfL := [" + ",\n    ".join(infs) + "]",
         f"  dmax := {DMAX}", f"  dmaxC := {DMAXC}\n", f"end {ns}", "end LeanResidy.X\n"]
    open(out_path, 'w').write("\n".join(L))
    print('ok', len(Dl), 'nämnarfaktorer')

main()
