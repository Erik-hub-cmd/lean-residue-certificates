"""Datafil för ett fall med TVÅ parametrar a (inre) och b (yttre):
Kin = Fr (Z4 A B) ppts (rationella funktioner i a), K = Fr Kin qpts (rationella funktioner i b med
koefficienter i Kin). Koefficienterna interpoleras exakt på ett rutnät och kontrolleras i alla punkter;
Lean kontrollerar sedan identiteterna själv."""
from fractions import Fraction as Fr
from par_common import fit_poly

def q(x):
    x = Fr(x)
    return f"({x.numerator} : ℚ)" if x.denominator == 1 else f"({x.numerator}/{x.denominator} : ℚ)"
def z4(c): return "⟨" + ", ".join(q(v) for v in c) + "⟩"

class G:  # Gaussiska rationella tal
    def __init__(s, re, im=0): s.re, s.im = Fr(re), Fr(im)
    def __sub__(s, o): return G(s.re - o.re, s.im - o.im)
    def __mul__(s, o): return G(s.re * o.re - s.im * o.im, s.re * o.im + s.im * o.re)

def gpow(x, n):
    r = G(1)
    for _ in range(n): r = r * x
    return r

class Fit2:
    def __init__(self, A1, A2, ppts, qpts, dA, dB):
        """ppts: lista av G (punkter i a-planet); qpts: lista av funktioner a -> G (punkter i b-planet)"""
        self.A1, self.A2, self.ppts, self.qpts, self.dA, self.dB = A1, A2, ppts, qpts, dA, dB
    def den_in(self, a, k):
        d = G(1)
        for p, e in zip(self.ppts, k): d = d * gpow(G(a) - p, e)
        assert d.im == 0, 'nämnarmallen i a är inte reell'
        return d.re
    def den_out(self, a, b, k):
        d = G(1)
        for p, e in zip(self.qpts, k): d = d * gpow(G(b) - p(a), e)
        assert d.im == 0, 'nämnarmallen i b är inte reell'
        return d.re
    def K(self, f, kin, kout):
        """f(a, b) -> 4-tupel; returnerar Lean-element i K"""
        # steg 1: för varje a, polynom i b
        rows = {}
        for a in self.A1:
            cs = []
            for c in range(4):
                ys = [Fr(f(a, b)[c]) * self.den_out(a, b, kout) for b in self.A2]
                co = fit_poly(self.A2, ys, self.dB); assert co is not None, ('b-interpolation', kout)
                cs.append(co)
            rows[a] = cs
        nb = max(len(c) for a in self.A1 for c in rows[a])
        out = []
        for j in range(nb):
            comps = []
            for c in range(4):
                ys = [(rows[a][c][j] if j < len(rows[a][c]) else Fr(0)) * self.den_in(a, kin) for a in self.A1]
                co = fit_poly(self.A1, ys, self.dA); assert co is not None, ('a-interpolation', kin, j)
                comps.append(co)
            n = max(len(c) for c in comps)
            coef = [tuple(c[i] if i < len(c) else Fr(0) for c in comps) for i in range(n)]
            while coef and all(x == 0 for x in coef[-1]): coef.pop()
            out.append(f"⟨[{', '.join(z4(c) for c in coef)}], {list(kin) if coef else []}⟩")
        while out and out[-1].startswith("⟨[]"): out.pop()
        return f"(⟨[{', '.join(out)}], {list(kout) if out else []}⟩ : K)"
