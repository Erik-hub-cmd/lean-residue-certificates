import sys, os, pickle
BR=os.environ.get('BRDIR','/root/lr/src/bevis_residy')
sys.path.insert(0, BR)
sys.dont_write_bytecode = True
from flint import fmpq

def q(x):
    try:
        x = fmpq(x)
    except TypeError:
        import sympy as sp
        x = sp.Rational(x); x = fmpq(int(x.p), int(x.q))
    p, d = int(x.p), int(x.q)
    return f"({p} : ℚ)" if d == 1 else f"({p}/{d} : ℚ)"

def lp(d):
    items = sorted(d.items())
    return "[" + ", ".join(f"(({a}, {b}), {q(c)})" for (a, b), c in items) + "]"

def z4(k, AB):
    return "(⟨" + ", ".join(q(c) for c in k.c) + f"⟩ : Z4 ({AB[0]}) ({AB[1]}))"

def edges(ed):
    return "[" + ", ".join(f"({i}, {j}, {n1}, {n2}, {q(w)})" for i, j, (n1, n2), w in ed) + "]"
