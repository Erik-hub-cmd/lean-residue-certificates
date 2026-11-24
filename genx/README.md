# Data generation for `LeanResidy/X` (not needed to build)

These scripts generated `LeanResidy/X/Data*.lean` and `LeanResidy/X/Case*.lean` (the three cases of the extension
`LeanResidy.X`, see `STATEMENTS.md` §7). Like `gen/`, they need the ancillary Python code of [E3]
(`residymetod_nya_fall/kod/`, always run on a copy, since `run.main` writes cache files) and `python-flint`; the
paths in them are those of the author's build directory.

* `gen_x.py`: [3².6²; 3.6.3.6] with unit conductances (field `ℚ(i, √2, √3)`).
* `probe3122.py`, `drive3122t.py`: 3.12² with conductance `t`; `run.main` at 14 rational `t`, then exact
  interpolation of every coefficient as a rational function of `t`.
* `probe488.py`, `drive488t.py`: 4.8² with conductances `(1 − c, 2c)`, `c = (u + u⁻¹)/2`, at 18 rational `u`,
  interpolated in `u`.
* `par_common.py`, `emit*.py`, `make_x.py`: shared code and the writer of the Lean files; `degeval.sh` computes the
  degree bound `dmax`.

Lean does not trust the interpolation or any other step here: a wrong coefficient makes the build fail.
