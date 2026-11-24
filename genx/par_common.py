"""Gemensamt för de parametriska fallen: kör run.main (i en KOPIA av koden) i många parametervärden
och samlar data (D, A i x-koordinater, T, parametrisering, partialbråk per post)."""
import sys, os, io, contextlib, pickle
from fractions import Fraction as Fr
BR = os.environ['BRDIR']
sys.path.insert(0, BR); sys.dont_write_bytecode = True
os.chdir(BR)
from flint import fmpq
import run as RUN
import nyfall, lat
from resmaskin import det_adj, Param

def fq(x): x = fmpq(x); return Fr(int(x.p), int(x.q))

def run_at(name, F, P, Fc):
    """run.main med given parametrisering P (x-koordinater) och graf Fc"""
    D, A = det_adj(*Fc)
    RUN.setup = lambda nm: (F, P, Fc, D, A)
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        F_, Pv, Dv, Av, loc, T, b0 = RUN.main(name)
    keys = [k for k in Pv.pts if k != F(0).key()] + [F(0).key()]
    PF = {}
    for kl, d in Av.items():
        if not d: continue
        e = {}
        for qk in loc:
            s = loc[qk][2][kl]; top = 1 if qk == 'inf' else 0
            for k in range(s.v, top):
                c = s.coef(k)
                if not c.is_zero(): e[(qk, -k)] = c
        PF[kl] = e
    return dict(D=D, A=A, T=T, Pv=Pv, keys=keys, PF=PF)

def param_from_tracks(F, trk):
    pts = {}; E = [{}, {}]
    for (h1, h2), a in trk:
        ex = (-h2, h1)
        for p, s in ((-a, 1), (a, -1)):
            pts[p.key()] = p
            for k in range(2):
                if ex[k]: E[k][p.key()] = E[k].get(p.key(), 0) + s * ex[k]
    E = [{p: n for p, n in e.items() if n} for e in E]
    return Param(F, pts, E, [F(1), F(1)])

def lagrange(xs, ys):
    """koefficienter (lägst först) för interpolationspolynomet"""
    n = len(xs); coef = [Fr(0)] * n
    for i in range(n):
        num = [Fr(1)]; den = Fr(1)
        for j in range(n):
            if j == i: continue
            num = [Fr(0)] + num
            for k in range(len(num) - 1): num[k] -= xs[j] * num[k + 1]
            den *= xs[i] - xs[j]
        for k in range(n): coef[k] += ys[i] * num[k] / den
    while coef and coef[-1] == 0: coef.pop()
    return coef

def peval(c, x):
    r = Fr(0)
    for a in reversed(c): r = r * x + a
    return r

def fit_poly(xs, ys, maxdeg):
    """polynom av grad ≤ maxdeg genom alla punkter (kontrolleras), annars None"""
    c = lagrange(xs[:maxdeg + 1], ys[:maxdeg + 1])
    if all(peval(c, x) == y for x, y in zip(xs, ys)): return c
    return None
