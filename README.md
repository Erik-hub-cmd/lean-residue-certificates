# lean-residue-certificates

Lean 4 proofs of the **finite exact computations** in the residue proofs of two papers on two-point resistances of
periodic resistor networks whose spectral curve is rational:

> **[E2]** Erik Ersson, *Isoradial partners for rational spectral curves on Archimedean and k-uniform tilings*
> (preprint, 2026), Section 6.2.
>
> **[E3]** Erik Ersson, *All two-point resistances on 3.6.3.6, 3.12², 4.8² and two two-uniform tilings in closed
> form* (preprint, 2026), proof of Theorem 1.

For eight lattices, and in the extension `LeanResidy.X` for three more cases (two of them for all values of a conductance), it proves, with all coefficients written out: the adjugate identity `M·A = D·I` for the Bloch
Laplacian, that the rational parametrisation lies on the spectral curve, and that the integrand of the residue
formula is *exactly* the stated sum of principal parts, for **all** `V²` matrix entries (so for every pair of
vertices) and for **every** choice of square roots (so for the parametrisation and its Galois conjugate).
The analysis around these computations (the cycle `Γ` and its integers, certified with interval arithmetic; the
integrability argument; the integral; Baker's theorem) is not formalised.

**For reviewers: read [`STATEMENTS.md`](STATEMENTS.md).** It lists the main theorems and every definition they use,
verbatim from the source (checked by a script in CI), with a plain-language reading, the sanity theorems that show
the statements are not vacuous, and the points to compare with the papers.

## Status

* Lean `v4.37.0-rc1`, Mathlib commit [`81cb93d`](https://github.com/leanprover-community/mathlib4/commit/81cb93dd9daa2d3d9cf275707da390fb66adadb0).
* No `sorry`, no `native_decide`, no new axioms. All heavy computations are done by the Lean kernel (`decide +kernel`).
* `lake env lean Axioms.lean` prints the axioms of the 33 main theorems and 105 sanity theorems (plus, for the two-parameter cases, 13 more); each depends only on
  `propext`, `Classical.choice` and `Quot.sound`. The CI checks this on every push.

| namespace | lattice | paper | `V` | entries | kernel time (1 core) |
|---|---|---|---|---|---|
| `C346` | 3⁴.6, conductance 4 on triangle–hexagon edges | [E2] | 6 | 36 | ~8 min |
| `C3` | [3.4².6; 3.6.3.6]₂, conductance 3/5 on square–square edges | [E2] | 5 | 25 | ~5 min |
| `C4612` | 4.6.12, conductance 1/5 on square–hexagon edges | [E2] | 12 | 144 | ~30 min |
| `Ckagome` | 3.6.3.6 | [E3] | 3 | 9 | <1 min |
| `C3122` | 3.12² | [E3] | 6 | 36 | ~1.5 min |
| `C3342` | 3³.4², conductance 3 on square–square edges | [E3] | 2 | 4 | <1 min |
| `C488` | 4.8² | [E3] | 4 | 16 | ~1 min |
| `Cf2b` | [3.4.3.12; 3.12²] | [E3] | 8 | 64 | ~4.5 min |

The extension `LeanResidy/X/` (generic over the coefficient model, see §7 of `STATEMENTS.md`) adds three cases:

| namespace | lattice | paper | `V` | entries | kernel time (1 core) | peak memory |
|---|---|---|---|---|---|---|
| `X.Cf2a` | [3².6²; 3.6.3.6], field `ℚ(i, √2, √3)` | [E3] | 3 | 9 | ~5 min | ~3 GB |
| `X.C3122t` | 3.12², conductance `t` on dodecagon–dodecagon edges, **all** `t ≠ 0, −3/2` | [E3] | 6 | 36 | ~20 min | ~6 GB |
| `X.C488u` | 4.8², conductances `(1 − c, 2c)`, `c = cos θ_t`, **all** `u = e^{iθ_t}` | [E3] | 4 | 16 | ~40 min | ~13.5 GB |

The families with **two** independent conductance ratios use a new coefficient model (§8 of `STATEMENTS.md`):
a polynomial in the two parameters is packed into four big integers (Kronecker substitution,
`X/Kron.lean`), so the kernel only does a few GMP multiplications per operation; the polynomial itself is
carried along as a delayed "ghost" with a proof that the packed numbers, an ℓ¹ coefficient bound and a degree
bound agree with it, and `kron_zero` shows that a packed value 0 with small coefficients forces the polynomial
to vanish. Denominators are products of a fixed list `Dl` of factors (`X/FrG.lean`).

| namespace | lattice | paper | `V` | entries | kernel time (1 core) | peak memory |
|---|---|---|---|---|---|---|
| `X.Cf2awK` | [3².6²; 3.6.3.6], **all** conductances (parameters `a = P₁`, `b = P₂`) | [E3] | 3 | 9 | ~1.5 min | ~3 GB |
| `X.Cf2bwK` | [3.4.3.12; 3.12²], **all** conductances (parameters `u`, `r`) | [E3] | 8 | 64 | ~9 min | ~5 GB |

The theorems hold for all parameter values at which no factor of `Dl` vanishes; `X/KronSanityUnit.lean` shows
that this includes the whole physical region (`f2a_hD_unit`, `f2b_hD_unit`). The data for these two cases
were produced by exact interpolation of the residue computation on a grid (`genk/`); Lean does not rely on
the interpolation.

## How it works

`Basic.lean` defines small computable models (ℚ, `ℚ(r, s)` with `r² = A`, `s² = B`, polynomials, rational functions
with denominators `∏(z − qᵢ)^{kᵢ}`, Laurent polynomials) and proves that their interpretation in any field of
characteristic 0 respects `+`, `·`, `−` and the zero test. An identity that the kernel has evaluated to
`isZero … = true` thus becomes an identity in the field.

* Theorems A and B are computed exactly in the model of rational functions (`Generic.lean`).
* Theorem C uses a degree bound plus point evaluation (`Points.lean`): the expression, multiplied by a suitable
  product of `(z − qᵢ)`, is a polynomial of degree at most `d` (computed from the exponents); the kernel evaluates
  it exactly at the `d + 1` integers `z = 2, …, d + 2`; a nonzero polynomial of degree `≤ d` has at most `d` roots.
* `Data<case>.lean` holds the data, generated by `gen/gen_case.py` from the Python code of the papers (see `gen/README.md`). Lean does not
  trust it: a wrong coefficient makes the build fail.
* `Sanity<case>.lean` holds the sanity theorems (§4 of `STATEMENTS.md`).
* `X/Generic.lean`, `X/Case.lean` prove the three theorems once for an arbitrary data package over an arbitrary
  coefficient model (`X/Basic.lean`: the degree-8 field `Z8`, rational functions in a conductance parameter);
  inverses at the check points are not proved correct but checked by multiplication (`invOK`). Data generated by
  `genx/`.

## Building

```
lake exe cache get     # Mathlib cache
lake build             # about 2 hours; 4.8² with weights needs about 13.5 GB of memory, [3.4.3.12; 3.12²] about 10 GB
lake env lean Axioms.lean
```
Lake builds independent files in parallel; on a machine with 16 GB this can run out of memory. The CI
therefore builds the cases one at a time (see `.github/workflows/build.yml`).

## Licence

Apache-2.0.
