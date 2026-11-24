import sys, os
sys.path.insert(0, os.path.expanduser('~/lr/genx'))
from par_common import *
from kfield import Field
F = Field(-1, -2)
i = F(0, 1)
us = [Fr(k, 11) for k in (2, 3, 4, 5, 6, 7, 8, 9, 13, 15, 16, 17, 18, 19, 20, 21, 23, 24)]
out = {}
for u in us:
    U = F(fmpq(u.numerator, u.denominator))
    trk = [((1, 0), F(1)), ((1, 0), U), ((0, 1), -i), ((0, 1), -i * U)]
    labels = {}
    for n, ((h, a), lab) in enumerate(zip(trk, ['1', 'u', '-i', '-iu'])):
        labels[(-a).key()] = ('-', lab); labels[a.key()] = ('+', lab)
    labels[F(0).key()] = ('0', '0')
    P = param_from_tracks(F, trk)
    c = (u + 1 / u) / 2
    Fc = lat.get('4.8^2', [1 - c, 2 * c])
    r = run_at(f'488u{u.numerator}_{u.denominator}', F, P, Fc)
    lab = lambda k: labels[k] if k != 'inf' else 'inf'
    out[u] = dict(D=r['D'], A=r['A'], T=r['T'], keys=[lab(k) for k in r['keys']],
                  E=[{lab(k): n for k, n in e.items()} for e in r['Pv'].E],
                  Ex=[{lab(k): n for k, n in e.items()} for e in P.E],
                  PF={kl: {(lab(k), m): tuple(fq(x) for x in v.c) for (k, m), v in e.items()} for kl, e in r['PF'].items()},
                  pts={lab(k): tuple(fq(x) for x in p.c) for k, p in r['Pv'].pts.items()})
    print(u, r['T'], flush=True)
pickle.dump(out, open(os.path.expanduser('~/lr/genx/raw488.pkl'), 'wb'))
