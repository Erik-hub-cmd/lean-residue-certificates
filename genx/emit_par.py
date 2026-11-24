"""Skriver en Data-fil för ett fall med EN parameter t: K = Fr (Z4 A B) tpts, tolkning i t.
Indata: rådata per parametervärde (probe*.py), nämnarmall (lista av exponenter per tpts-punkt) för
partialbråkens koefficienter. Allt interpoleras exakt och kontrolleras i alla punkter här; Lean kontrollerar
sedan identiteterna på nytt, så interpolationen behöver inte litas på."""
import os
from fractions import Fraction as Fr
from par_common import lagrange, peval, fit_poly

def q(x):
    x = Fr(x)
    return f"({x.numerator} : ℚ)" if x.denominator == 1 else f"({x.numerator}/{x.denominator} : ℚ)"

def z4(c): return "⟨" + ", ".join(q(v) for v in c) + "⟩"

def emit(name, R, AB, tpts, pfk, title, maxdeg=12, edge_w=None, V=None, Ered=None):
    """R: {t: dict(D, A, T, keys, E, PF, pts)}; tpts: list av rationella tal (punkterna i t-planet);
    pfk: exponentlista för PF-nämnaren; edge_w: funktion klass -> Fr-element i t (koefficientlista)"""
    ts = sorted(R); r0 = R[ts[0]]
    for t in ts:
        assert R[t]['T'] == r0['T'] and R[t]['keys'] == r0['keys'] and R[t]['E'] == r0['E']
        assert R[t]['pts'] == r0['pts']
    def den(t, k):
        d = Fr(1)
        for p, e in zip(tpts, k): d *= (t - p) ** e
        return d
    def fitK(vals, k):
        """vals: lista (per t) av 4-tupler; returnerar Lean-element ⟨[z4..], k⟩"""
        comps = []
        for c in range(4):
            ys = [v[c] * den(t, k) for v, t in zip(vals, ts)]
            co = fit_poly(ts, ys, maxdeg)
            assert co is not None, 'interpolationen misslyckades'
            comps.append(co)
        n = max(len(c) for c in comps)
        coef = [tuple(c[i] if i < len(c) else Fr(0) for c in comps) for i in range(n)]
        return f"(⟨[{', '.join(z4(c) for c in coef)}], {list(k)}⟩ : K)"
    def fitQ(vals):
        co = fit_poly(ts, [Fr(v) for v in vals], maxdeg); assert co is not None
        return f"(⟨[{', '.join(z4((c, 0, 0, 0)) for c in co)}], []⟩ : K)"
    keys = r0['keys']; idx = {k: i for i, k in enumerate(keys)}
    ex = lambda k: "[" + ", ".join(str(r0['E'][k].get(kk, 0)) for kk in keys) + "]"
    # D och A i x-koordinater (rationella koefficienter, polynom i t)
    def lpfit(get):
        mons = set()
        for t in ts: mons |= set(get(R[t]))
        return "[" + ", ".join(f"(({a}, {b}), {fitQ([get(R[t]).get((a, b), 0) for t in ts])})"
                               for (a, b) in sorted(mons)) + "]"
    from flint import fmpq
    cv = lambda x: Fr(int(fmpq(x).p), int(fmpq(x).q))
    Dfit = lpfit(lambda r: {k: cv(v) for k, v in r['D'].items()})
    Afit = [lpfit(lambda r, i=i, j=j: {k: cv(v) for k, v in r['A'].get((i, j), {}).items()})
            for i in range(V) for j in range(V)]
    fin_all, inf_all = [], []
    for i in range(V):
        for j in range(V):
            ks = set()
            for t in ts: ks |= set(R[t]['PF'].get((i, j), {}))
            fin, inf = [], []
            for (qk, m) in sorted(ks, key=lambda x: (str(x[0]), x[1])):
                vals = [R[t]['PF'].get((i, j), {}).get((qk, m), (0, 0, 0, 0)) for t in ts]
                el = fitK(vals, pfk)
                if qk == 'inf': inf.append(f"({m}, {el})")
                else: fin.append(f"({idx[qk]}, {m}, {el})")
            fin_all.append("[" + ", ".join(fin) + "]"); inf_all.append("[" + ", ".join(inf) + "]")
    T = r0['T']
    tp = "[" + ", ".join(f"(⟨{q(p)}, 0, 0, 0⟩ : Z4 ({AB[0]}) ({AB[1]}))" for p in tpts) + "]"
    ptsL = "[" + ", ".join(f"(⟨[{z4(r0['pts'][k])}], []⟩ : K)" for k in keys) + "]"
    L = ["import LeanResidy.X.Case\n",
         f"/-! Genererad av genx/ ({name}): exakt interpolation i parametern ur run.main i en kopia av\n"
         "residymetod_nya_fall/kod. Lean kontrollerar identiteterna själv. -/\n",
         "namespace LeanResidy.X", f"namespace C{name}\n",
         f"/-- punkterna i parameterplanet (nämnarnas nollställen) -/\nabbrev tpts : List (Z4 ({AB[0]}) ({AB[1]})) := {tp}",
         f"/-- koefficientmodellen: rationella funktioner i parametern med nämnare ∏ (t − tptsᵢ)^kᵢ -/\nabbrev K := Fr (Z4 ({AB[0]}) ({AB[1]})) tpts\n",
         "def data : Case K where",
         f"  V := {V}",
         f"  E := {Ered}",
         "  AL := [" + ",\n    ".join(Afit) + "]",
         f"  D := {Dfit}",
         f"  pts := {ptsL}",
         f"  ex1 := EX1", f"  ex2 := EX2",
         f"  t00 := {T[0][0]}", f"  t01 := {T[0][1]}", f"  t10 := {T[1][0]}", f"  t11 := {T[1][1]}",
         f"  ev1 := {ex(0)}", f"  ev2 := {ex(1)}",
         "  PFfinL := [" + ",\n    ".join(fin_all) + "]",
         "  PFinfL := [" + ",\n    ".join(inf_all) + "]",
         "  dmax := DMAX\n", f"end C{name}", "end LeanResidy.X\n"]
    return "\n".join(L)
