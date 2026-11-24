"""Datafil för ett fall med EN parameter (t eller u): K = Fr (Z4 A B) tpts.
Varje koefficient c(t) ∈ ℚ(r,s)(t) skrivs som N(t)/∏(t − tptsᵢ)^kᵢ med en mall k och en rationell
nämnarfunktion den(t) = ∏(t − tptsᵢ)^kᵢ (mallarna väljs så att den är rationell). N interpoleras exakt
komponentvis och kontrolleras i alla punkter; Lean kontrollerar sedan identiteterna själv."""
from fractions import Fraction as Fr
from par_common import fit_poly

def q(x):
    x = Fr(x)
    return f"({x.numerator} : ℚ)" if x.denominator == 1 else f"({x.numerator}/{x.denominator} : ℚ)"
def z4(c): return "⟨" + ", ".join(q(v) for v in c) + "⟩"

class Fit:
    def __init__(self, ts, den, maxdeg):
        self.ts, self.den, self.maxdeg = ts, den, maxdeg
    def K(self, vals, k):
        """vals: per t en 4-tupel (komponenter i basen 1, r, s, rs); k: mallnamn"""
        comps = []
        for c in range(4):
            ys = [Fr(v[c]) * self.den(t, k) for v, t in zip(vals, self.ts)]
            co = fit_poly(self.ts, ys, self.maxdeg)
            assert co is not None, ('interpolationen misslyckades', k)
            comps.append(co)
        n = max(len(c) for c in comps)
        coef = [tuple(c[i] if i < len(c) else Fr(0) for c in comps) for i in range(n)]
        while coef and all(x == 0 for x in coef[-1]): coef.pop()
        return f"(⟨[{', '.join(z4(c) for c in coef)}], {list(k)}⟩ : K)"

def lp_fit(fit, dicts, k):
    """dicts: per t ett Laurentpolynom {(a, b): rationellt}"""
    mons = set()
    for d in dicts: mons |= set(d)
    return "[" + ", ".join(f"(({a}, {b}), {fit.K([(d.get((a, b), 0), 0, 0, 0) for d in dicts], k)})"
                           for (a, b) in sorted(mons)) + "]"

def pf_fit(fit, R, ts, V, idx, k):
    fin_all, inf_all = [], []
    for i in range(V):
        for j in range(V):
            ks = set()
            for t in ts: ks |= set(R[t]['PF'].get((i, j), {}))
            fin, inf = [], []
            for (qk, m) in sorted(ks, key=lambda x: (str(x[0]), x[1])):
                vals = [R[t]['PF'].get((i, j), {}).get((qk, m), (0, 0, 0, 0)) for t in ts]
                el = fit.K(vals, k)
                if qk == 'inf': inf.append(f"({m}, {el})")
                else: fin.append(f"({idx[qk]}, {m}, {el})")
            fin_all.append("[" + ", ".join(fin) + "]"); inf_all.append("[" + ", ".join(inf) + "]")
    return fin_all, inf_all

def write(path, name, doc, AB, tptsL, V, Ered, Afit, Dfit, ptsL, ex1, ex2, T, ev1, ev2, fin_all, inf_all):
    L = ["import LeanResidy.X.Case\n",
         f"/-! Genererad av genx/ ({name}). {doc}\n"
         "Koefficienterna är exakt interpolerade i parametern ur run.main (kopia av residymetod_nya_fall/kod);\n"
         "Lean kontrollerar identiteterna själv, så interpolationen behöver inte litas på. -/\n",
         "namespace LeanResidy.X", f"namespace C{name}\n",
         f"/-- punkterna i parameterplanet (nämnarnas nollställen och inverserna i kontrollpunkterna) -/\n"
         f"abbrev tpts : List (Z4 ({AB[0]}) ({AB[1]})) := {tptsL}",
         f"/-- koefficientmodellen: rationella funktioner i parametern med nämnare ∏ (t − tptsᵢ)^kᵢ -/\n"
         f"abbrev K := Fr (Z4 ({AB[0]}) ({AB[1]})) tpts\n",
         "def data : Case K where", f"  V := {V}", f"  E := {Ered}",
         "  AL := [" + ",\n    ".join(Afit) + "]", f"  D := {Dfit}", f"  pts := {ptsL}",
         f"  ex1 := {ex1}", f"  ex2 := {ex2}",
         f"  t00 := {T[0][0]}", f"  t01 := {T[0][1]}", f"  t10 := {T[1][0]}", f"  t11 := {T[1][1]}",
         f"  ev1 := {ev1}", f"  ev2 := {ev2}",
         "  PFfinL := [" + ",\n    ".join(fin_all) + "]", "  PFinfL := [" + ",\n    ".join(inf_all) + "]",
         "  dmax := DMAX\n", f"end C{name}", "end LeanResidy.X\n"]
    open(path, 'w').write("\n".join(L))
