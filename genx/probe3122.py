import sys, os
sys.path.insert(0, os.path.expanduser('~/lr/genx'))
from par_common import *
import sympy as sp
F = nyfall.field('3122')
P = param_from_tracks(F, nyfall.tracks('3122'))
ts = [Fr(k, 7) for k in range(3, 3 + 14)]
R = {}
for t in ts:
    Fc = lat.get(nyfall.NAMES['3122'], [1, t])
    R[t] = run_at(f'3122t{t.numerator}_{t.denominator}', F, P, Fc)
    print(t, R[t]['T'], len(R[t]['PF']), flush=True)
pickle.dump({t: dict(D=r['D'], A=r['A'], T=r['T'], keys=r['keys'], E=r['Pv'].E,
                     PF={kl: {k: tuple(fq(x) for x in v.c) for k, v in e.items()} for kl, e in r['PF'].items()},
                     pts={k: tuple(fq(x) for x in p.c) for k, p in r['Pv'].pts.items()})
             for t, r in R.items()}, open(os.path.expanduser('~/lr/genx/raw3122.pkl'), 'wb'))
