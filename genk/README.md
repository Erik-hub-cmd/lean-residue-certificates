# genk: data generators for the two-parameter cases

* `fit2.py` — [3.4.3.12; 3.12²] with all conductances: interpolates every coefficient exactly as a rational
  function of `(u, r)` from runs of the residue computation on a grid (u = k/11, 26 values; r = k/5, 20 values),
  checks the interpolant at all grid points, and writes `LeanResidy/X/Dataf2bwK.lean`.
* `conv.py` — [3².6²; 3.6.3.6] with all conductances: rewrites an earlier exactly interpolated data file (nested
  rational functions) into the packed model, `LeanResidy/X/Dataf2awK.lean`.
* `mkcase.py` — writes the case files `Case*K.lean` (kernel checks + theorems).

The residue computation itself (`run.main`) is not part of this repository. Lean does not rely on these
scripts: a wrong coefficient makes a kernel check fail, it cannot produce a false theorem.
