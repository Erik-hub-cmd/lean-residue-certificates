# Data generation (not needed to build)

These scripts generated `LeanResidy/Data<case>.lean` and `LeanResidy/Case<case>.lean`. They need the ancillary
Python code of the papers ([E2]: `bevis_residy/`, [E3]: `residymetod_nya_fall/kod/`, set with `BRDIR`) and
`python-flint`; the paths in them are those of the author's build directory. Lean does not depend on them: the
generated files are checked by the kernel. `make_case.py` copies `Case346.lean` to the other cases; the case-specific
comments in the generated files were edited by hand afterwards.
