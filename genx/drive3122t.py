import sys, os, pickle
sys.path.insert(0, os.path.expanduser('~/lr/genx'))
from par_common import *
from emit_par import emit, z4
F = nyfall.field('3122')
P = param_from_tracks(F, nyfall.tracks('3122'))
R = pickle.load(open(os.path.expanduser('~/lr/genx/raw3122.pkl'), 'rb'))
r0 = R[sorted(R)[0]]
V, ed = lat.get(nyfall.NAMES['3122'], ['c0', 'c1'])
wl = {'c0': "(⟨[⟨1, 0, 0, 0⟩], []⟩ : K)", 'c1': "(⟨[⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩], []⟩ : K)"}
Ered = "[" + ", ".join(f"({i}, {j}, {n1}, {n2}, {wl[w]})" for i, j, (n1, n2), w in ed) + "]"
s = emit('3122t', R, (-3, -1), [Fr(0), Fr(-3, 2)], [1, 1], '3.12² med vikt t', maxdeg=7, V=V, Ered=Ered)
keys = r0['keys']
ex = lambda k: "[" + ", ".join(str(P.E[k].get(kk, 0)) for kk in keys) + "]"
s = s.replace('EX1', ex(0)).replace('EX2', ex(1))
open(os.path.expanduser('~/lr/LeanResidy/X/Data3122t.lean'), 'w').write(s)
print('ok', len(s))
