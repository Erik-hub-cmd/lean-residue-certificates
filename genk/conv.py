"""Konvertera ett gammalt datapaket (Fr (Fr Z4 ppts) qpts, två parametrar a, b) till den
Kroneckerpackade modellen FrG (PK A B Kb S) Dl.

Användning: python3 conv.py GAMMAL.lean NY.lean NAMESPACE Kb S QMAX

Varje K-element  (Σ_j kin_j(a) b^j) / Π_m (b − q_m(a))^{e_m},  kin_j = poly_j(a) / Π_l (a − p_l)^{k_jl}
skrivs om till   N(a, b) / Π Dl^k  med N ett polynom i a, b över ℤ[r, s] (delat med ett heltal).
Faktorer b − c/a skrivs som (ab − c)/a (täljaren får a^e). Lean kontrollerar allt själv; den här
filen bara skriver om datat.
"""
import sys, re
from fractions import Fraction as Q
from math import lcm

A, B = None, None

# ---------- parser för Lean-literaler ----------
def tokenize(s):
    s = re.sub(r':\s*(ℚ|K|Kin)\)', ')', s)
    toks = re.findall(r'⟨|⟩|\[|\]|\(|\)|,|-?\d+/\d+|-?\d+', s)
    return toks

def parse(toks, i=0):
    t = toks[i]
    if t == '⟨' or t == '[' or t == '(':
        close = {'⟨': '⟩', '[': ']', '(': ')'}[t]
        items = []; i += 1
        while toks[i] != close:
            x, i = parse(toks, i)
            items.append(x)
            if toks[i] == ',': i += 1
        i += 1
        if t == '(' and len(items) == 1: return items[0], i
        return (('T' if t == '⟨' else 'L' if t == '[' else 'P'), items), i
    return Q(t), i + 1

def lit(s):
    x, i = parse(tokenize(s)); return x

def field(src, name):
    m = re.search(r'\n  ' + name + r' := ', src)
    j = m.end(); depth = 0; k = j
    while True:
        c = src[k]
        if c in '[⟨(': depth += 1
        elif c in ']⟩)': depth -= 1
        if depth == 0 and (c == '\n' and src[k + 1:k + 3] == '  ' and src[k + 3] != ' '): break
        if depth == 0 and src[k] == '\n' and not src[k + 1:].startswith('    '): break
        k += 1
    return src[j:k]

# ---------- Z4 och polynom i (a, b) ----------
def zmul(x, y):
    return (x[0]*y[0] + A*x[1]*y[1] + B*x[2]*y[2] + A*B*x[3]*y[3],
            x[0]*y[1] + x[1]*y[0] + B*(x[2]*y[3] + x[3]*y[2]),
            x[0]*y[2] + x[2]*y[0] + A*(x[1]*y[3] + x[3]*y[1]),
            x[0]*y[3] + x[3]*y[0] + x[1]*y[2] + x[2]*y[1])
def zadd(x, y): return tuple(u + v for u, v in zip(x, y))
Z0 = (Q(0),) * 4; Z1 = (Q(1), Q(0), Q(0), Q(0))
def iszero(x): return all(u == 0 for u in x)

def padd(p, q):
    r = dict(p)
    for k, v in q.items():
        r[k] = zadd(r.get(k, Z0), v)
        if iszero(r[k]): del r[k]
    return r
def pmul(p, q):
    r = {}
    for k1, v1 in p.items():
        for k2, v2 in q.items():
            k = (k1[0] + k2[0], k1[1] + k2[1])
            r[k] = zadd(r.get(k, Z0), zmul(v1, v2))
    return {k: v for k, v in r.items() if not iszero(v)}
def ppow(p, n):
    r = {(0, 0): Z1}
    for _ in range(n): r = pmul(r, p)
    return r
def pconst(z): return {} if iszero(z) else {(0, 0): z}

def z4(t):
    assert t[0] == 'T' and len(t[1]) == 4, t
    return tuple(Q(u) for u in t[1])

# ---------- gamla modellen ----------
def kin_parts(x):
    """Kin = ⟨[Z4..], [k..]⟩ -> (poly i a, kvektor)"""
    assert x[0] == 'T'
    num, k = x[1]
    p = {}
    for i, z in enumerate(num[1]):
        zz = z4(z)
        if not iszero(zz): p[(i, 0)] = zz
    return p, [int(u) for u in k[1]]

class Conv:
    def __init__(self, ppts, qpts):
        self.ppts = [z4(p) for p in ppts]          # punkter i a-planet (Z4)
        self.qpts = [kin_parts(q) for q in qpts]   # punkter i b-planet (Kin)
        self.Dl = []; self.Dkey = {}
    def dl_index(self, poly, name):
        key = tuple(sorted(poly.items()))
        if key not in self.Dkey:
            self.Dkey[key] = len(self.Dl); self.Dl.append((poly, name))
        return self.Dkey[key]
    def afac(self, l):  # a − p_l
        p = self.ppts[l]
        return padd({(1, 0): Z1}, pconst(tuple(-u for u in p)))
    def bfac(self, m):
        """b − q_m(a) = fac / a^e ; returnerar (fac, e)"""
        qp, qk = self.qpts[m]
        if all(u == 0 for u in qk):
            return padd({(0, 1): Z1}, {k: tuple(-u for u in v) for k, v in qp.items()}), 0
        # q = c / (a - ppts_0)^1 med ppts_0 = 0
        assert iszero(self.ppts[0]) and qk[0] == 1 and sum(qk) == 1 and set(qp) <= {(0, 0)}, (qp, qk)
        c = qp.get((0, 0), Z0)
        return padd({(1, 1): Z1}, pconst(tuple(-u for u in c))), 1
    def K(self, x):
        """K = ⟨[Kin..], [kout..]⟩ -> (N poly i (a,b), dict Dl-index -> exponent)"""
        assert x[0] == 'T'
        kins, kout = x[1]
        parts = [kin_parts(k) for k in kins[1]]
        kout = [int(u) for u in kout[1]]
        L = max([len(k) for _, k in parts] + [0])
        kmax = [max([k[l] if l < len(k) else 0 for _, k in parts] + [0]) for l in range(L)]
        N = {}
        for j, (p, k) in enumerate(parts):
            q = p
            for l in range(L):
                e = kmax[l] - (k[l] if l < len(k) else 0)
                if e: q = pmul(q, ppow(self.afac(l), e))
            q = {(i, jj + j): v for (i, jj), v in q.items()}
            N = padd(N, q)
        den = {}
        for l in range(L):
            if kmax[l]:
                idx = self.dl_index(self.afac(l), f"a-p{l}")
                den[idx] = den.get(idx, 0) + kmax[l]
        for m, e in enumerate(kout):
            if e:
                fac, ea = self.bfac(m)
                idx = self.dl_index(fac, f"b-q{m}")
                den[idx] = den.get(idx, 0) + e
                if ea: N = pmul(N, ppow({(1, 0): Z1}, e * ea))
        return N, den

# ---------- utskrift ----------
def poly_lean(p):
    """-> (termlista med heltal, den)"""
    d = 1
    for v in p.values():
        for u in v: d = lcm(d, u.denominator)
    terms = []
    for (i, j), v in sorted(p.items()):
        c = [int(u * d) for u in v]
        terms.append(f"(({i}, {j}), ⟨{c[0]}, {c[1]}, {c[2]}, {c[3]}⟩)")
    return "[" + ", ".join(terms) + "]", d

def pk_lean(p):
    t, d = poly_lean(p)
    return f"mk {t} {d}"

def main():
    global A, B
    src_path, out_path, ns, Kb, S, QMAX = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
    src = open(src_path).read()
    m = re.search(r'abbrev ppts : List \(Z4 \((-?\d+)\) \((-?\d+)\)\) := (\[.*?\])\n', src)
    A, B = int(m.group(1)), int(m.group(2))
    ppts = lit(m.group(3))[1]
    m2 = re.search(r'abbrev qpts : List Kin := (\[.*?\])\n', src)
    qpts = lit(m2.group(1))[1]
    cv = Conv(ppts, qpts)
    def K(x):
        N, den = cv.K(x)
        return (N, den)
    V = int(field(src, 'V'))
    E = lit(field(src, 'E'))[1]
    AL = lit(field(src, 'AL'))[1]
    D = lit(field(src, 'D'))[1]
    pts = lit(field(src, 'pts'))[1]
    PFfin = lit(field(src, 'PFfinL'))[1]
    PFinf = lit(field(src, 'PFinfL'))[1]
    simple = {f: field(src, f) for f in ['ex1', 'ex2', 't00', 't01', 't10', 't11', 'ev1', 'ev2', 'dmax']}
    dmaxC = field(src, 'dmaxC') if '\n  dmaxC := ' in src else '0'
    Es = [(int(e[1][0]), int(e[1][1]), int(e[1][2]), int(e[1][3]), K(e[1][4])) for e in E]
    def LP(L): return [((int(t[1][0][1][0]), int(t[1][0][1][1])), K(t[1][1])) for t in L[1]]
    ALs = [LP(L) for L in AL]
    Ds = LP(('L', D))
    ptss = [K(p) for p in pts]
    fins = [[(int(t[1][0]), int(t[1][1]), K(t[1][2])) for t in f[1]] for f in PFfin]
    infs = [[(int(t[1][0]), K(t[1][1])) for t in f[1]] for f in PFinf]
    # kontrollpunkternas faktorer q − pt (för inverserna)
    for (N, den) in ptss:
        assert not den, "punktering med nämnare"
        if all(k == (0, 0) for k in N): continue
        for q in range(2, QMAX + 1):
            w = padd(pconst((Q(q), Q(0), Q(0), Q(0))), {k: tuple(-u for u in v) for k, v in N.items()})
            cv.dl_index(w, f"{q}-pt")
    nD = len(cv.Dl)
    def kvec(den): return "[" + ", ".join(str(den.get(i, 0)) for i in range(max(den.keys(), default=-1) + 1)) + "]"
    def Kl(x):
        N, den = x
        return f"(⟨{pk_lean(N)}, {kvec(den)}⟩ : K)"
    out = []
    out.append("import LeanResidy.X.Case\nimport LeanResidy.X.FrG\n")
    out.append(f"/-! Genererad av genk/conv.py ur {src_path.split('/')[-1]}: samma data, omskriven till den\n"
               "Kroneckerpackade modellen `FrG (PK A B Kb S) Dl` (täljare = polynom i a, b; nämnare = potenser av\n"
               "faktorerna i `Dl`). Lean kontrollerar identiteterna själv. -/\n")
    out.append("set_option maxRecDepth 100000\n")
    out.append(f"namespace LeanResidy.X\nnamespace {ns}\n")
    out.append(f"abbrev PKf := PK ({A}) ({B}) {Kb} {S}")
    out.append("/-- ett data-element `P / den` -/\nabbrev mk (P : GP) (den : ℕ) : PKf := PK.ofList' P den\n")
    out.append("/-- nämnarfaktorerna -/\ndef Dl : List PKf := [" + ",\n  ".join(
        f"{pk_lean(p)}" for p, nm in cv.Dl) + "]\n")
    out.append("/-- vad faktorerna är (kommentar): " + "; ".join(f"{i}: {nm}" for i, (p, nm) in enumerate(cv.Dl)) + " -/\n")
    out.append("abbrev K := FrG PKf Dl\n")
    out.append("def data : Case K where")
    out.append(f"  V := {V}")
    out.append("  E := [" + ", ".join(f"({i}, {j}, {n1}, {n2}, {Kl(w)})" for i, j, n1, n2, w in Es) + "]")
    def LPl(L): return "[" + ", ".join(f"(({e[0]}, {e[1]}), {Kl(c)})" for e, c in L) + "]"
    out.append("  AL := [" + ",\n    ".join(LPl(L) for L in ALs) + "]")
    out.append(f"  D := {LPl(Ds)}")
    out.append("  pts := [" + ", ".join(Kl(p) for p in ptss) + "]")
    for f in ['ex1', 'ex2', 't00', 't01', 't10', 't11', 'ev1', 'ev2']:
        out.append(f"  {f} := {simple[f]}")
    out.append("  PFfinL := [" + ",\n    ".join("[" + ", ".join(f"({a}, {b}, {Kl(c)})" for a, b, c in f) + "]" for f in fins) + "]")
    out.append("  PFinfL := [" + ",\n    ".join("[" + ", ".join(f"({a}, {Kl(c)})" for a, c in f) + "]" for f in infs) + "]")
    out.append(f"  dmax := {simple['dmax'].strip()}")
    out.append(f"  dmaxC := {dmaxC.strip()}\n")
    out.append(f"end {ns}\nend LeanResidy.X\n")
    open(out_path, 'w').write("\n".join(out))
    print("Dl:", nD, [nm for p, nm in cv.Dl])
    # statistik
    degs = [max([k[0] for k in N] + [0]) for _, (N, d) in [(0, c) for L in ALs for _, c in L]]
    degb = [max([k[1] for k in N] + [0]) for _, (N, d) in [(0, c) for L in ALs for _, c in L]]
    print("A: max deg a", max(degs), "max deg b", max(degb))

main()
