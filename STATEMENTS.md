# What is proved: the statements, verbatim, with a plain reading

This file is for reviewers. **You do not need to read any proofs.** Lean's kernel has checked them: the build has
no `sorry`, no `native_decide`, and `Axioms.lean` shows that every theorem listed below depends only on `propext`,
`Classical.choice` and `Quot.sound`. What Lean cannot check is whether the *definitions and statements* mean what
the papers mean. That is what this file is for. Every Lean block below is copied verbatim from the source by a
script (`scripts/check_statements.py` checks this in CI).

References:
* **[E2]** Erik Ersson, *Isoradial partners for rational spectral curves on Archimedean and k-uniform tilings*
  (draft, version 2, November 2026), subsection "Proof of Theorem `thm:allpairs`", Lemma `lem:param` and Lemma 11 (`lem:poles`).
* **[E3]** Erik Ersson, *All two-point resistances on 3.6.3.6, 3.12², 4.8² and two two-uniform tilings in closed
  form* (draft, version 6, November 2026), section "Proof of Theorem `thm:main`", Lemmas `lem:param` and `lem:poles`.

Questions for a reviewer are marked **[check]**.

## 0. What the formalisation covers, in one paragraph

The residue proofs in [E2] and [E3] compute every two-point resistance from a rational parametrisation
`z ↦ x(z)` of the spectral curve `{P = 0}`, `P = det M`, of the Bloch Laplacian `M(x)`. They need three exact
algebraic facts per lattice, which were checked by computer algebra in Python: (A) `adj M / P` is the inverse of
`M`; (B) `P(x(z)) ≡ 0`; (C) for **every** entry `(k, l)` the integrand
`ρ_kl = adj M_kl(x(z)) · v₁'(z)/v₁(z) / (v₂ ∂_{v₂} P)(v(z))` equals an explicit sum of principal parts at the
punctures (Lemma `lem:poles`(a)). This repository re-proves (A), (B), (C) in Lean for eight lattices, with all
coefficients written out, for every choice of square roots (so for the parametrisation *and* its Galois conjugate).
Everything else in the proofs — birationality, the cycle `Γ` and the integers `k_q` (interval arithmetic), the
integrability argument that removes the poles at `0` and `∞` from `ρ_f`, the integral itself, Baker's theorem — is
**not** formalised.

## 1. The cases

| namespace | lattice | paper | conductances | `K = ℚ(r, s)` | `V` | entries |
|---|---|---|---|---|---|---|
| `C346` | 3⁴.6 | [E2] | 4 on triangle–hexagon edges, else 1 | `r² = −3, s² = −35` | 6 | 36 |
| `C3` | [3.4².6; 3.6.3.6]₂ | [E2] | 3/5 on square–square edges, else 1 | `r² = −33, s² = −341` | 5 | 25 |
| `C4612` | 4.6.12 | [E2] | 1/5 on square–hexagon edges, else 1 | `r² = −3, s² = −2` | 12 | 144 |
| `Ckagome` | 3.6.3.6 | [E3] | 1 | `r² = −3` (`s² = −1` unused) | 3 | 9 |
| `C3122` | 3.12² | [E3] | 1 | `r² = −3` (`s² = −1` unused) | 6 | 36 |
| `C3342` | 3³.4² | [E3] | 3 on square–square edges, else 1 | `r² = −3` (`s² = −1` unused) | 2 | 4 |
| `C488` | 4.8² | [E3] | 1 | `r² = −1, s² = −2` | 4 | 16 |
| `Cf2b` | [3.4.3.12; 3.12²] | [E3] | 1 | `r² = −1, s² = −35` | 8 | 64 |

Not included: [3².6²; 3.6.3.6] of [E3] (its field `ℚ(i, √2, √3)` has degree 8), and all results with variable
conductances in [E3], section "General conductances".

The data of each case (`V`, `E`, `D`, `A`, `pts`, `ex1`, `ex2`, `t00…t11`, `ev1`, `ev2`, `PFfinL`, `PFinfL`) are in
`LeanResidy/Data<case>.lean`, generated from the Python code of the papers. **Lean does not trust them**: if any
coefficient were wrong, a theorem below would fail to compile. What Lean cannot know is whether the data describe the
lattice of the paper; see §5.

## 2. Definitions (shared by all cases)

`F` is always a field; in the main theorems it has characteristic 0 (for example `ℂ`).

```lean
abbrev LP := List ((ℤ × ℤ) × ℚ)
def leval (L : LP) (x1 x2 : F) : F := (L.map fun t => (t.2 : F) * x1 ^ t.1.1 * x2 ^ t.1.2).sum
```
A Laurent polynomial is a list of terms `((i, j), c)`, meaning `c · x₁^i · x₂^j`; `leval` evaluates it.

```lean
abbrev Edge := ℕ × ℕ × ℤ × ℤ × ℚ
def edgeC (x1 x2 : F) (i j : ℕ) (e : Edge) : F :=
  let a := e.1; let b := e.2.1; let n1 := e.2.2.1; let n2 := e.2.2.2.1; let w : F := e.2.2.2.2
  (if i = a ∧ j = a then w else 0) + (if i = b ∧ j = b then w else 0)
    - (if i = a ∧ j = b then w * (x1 ^ n1 * x2 ^ n2) else 0)
    - (if i = b ∧ j = a then w * (x1 ^ n1 * x2 ^ n2)⁻¹ else 0)
def lapMat (V : ℕ) (E : List Edge) (x1 x2 : F) : Matrix (Fin V) (Fin V) F :=
  fun i j => (E.map (edgeC x1 x2 i j)).sum
```
An edge `(a, b, n₁, n₂, w)` of the quotient graph joins vertex `a` in cell `0` to vertex `b` in cell `(n₁, n₂)` with
conductance `w`. `lapMat V E x` is the Bloch Laplacian: `M_aa += w`, `M_bb += w`, `M_ab −= w x^n`,
`M_ba −= w x^{−n}`. **[check]** This is the matrix of the quadratic form `Σ_e w_e |u_a − x^{n_e} u_b|²` used in
[E2, Lemma 12]; the opposite sign convention would only replace `x` by `x⁻¹` throughout.

```lean
def lmat (V : ℕ) (A : ℕ → ℕ → LP) (x1 x2 : F) : Matrix (Fin V) (Fin V) F :=
  fun i j => leval (A i j) x1 x2
def xpar (qs : List F) (es : List ℤ) (z : F) : F := (List.zipWith (fun q e => (z - q) ^ e) qs es).prod
def dlogv (qs : List F) (es : List ℤ) (z : F) : F :=
  ((List.range es.length).map fun i => (es.getD i 0 : F) / (z - qs.getD i 0)).sum
def trL (t00 t01 t10 t11 : ℤ) (L : LP) : LP :=
  L.map fun t => ((t00 * t.1.1 + t01 * t.1.2, t10 * t.1.1 + t11 * t.1.2), t.2)
def eul (L : LP) : LP := L.map fun t => (t.1, t.2 * t.1.2)
def pfval (qs : List F) (fin : List (ℕ × ℕ × F)) (inf : List (ℕ × F)) (z : F) : F :=
  (fin.map fun t => t.2.2 / (z - qs.getD t.1 0) ^ t.2.1).sum + (inf.map fun t => t.2 * z ^ t.1).sum
```
* `lmat V A x` is the matrix with entries the Laurent polynomials `A i j` evaluated at `x`.
* `xpar qs es z = ∏ᵢ (z − qᵢ)^{eᵢ}` is the parametrisation (eq. `xz` of [E2]).
* `dlogv qs es z = Σᵢ eᵢ/(z − qᵢ)`, the logarithmic derivative of `xpar qs es`. **[check]** This is a definition by
  the formula, not a theorem about derivatives.
* `trL T L` changes coordinates: the monomial with exponent `n` gets exponent `T n`, i.e. `x^n = v^{Tn}` as in
  [E2, Step 2]. Proved: `leval (trL T L) v₁ v₂ = leval L (v₁^{t00} v₂^{t10}, v₁^{t01} v₂^{t11})` (`leval_trL`).
* `eul L` multiplies the term `c v₁^a v₂^b` by `b`: it is the operator `v₂ ∂/∂v₂`. **[check]** Again a definition
  by the formula.
* `pfval qs fin inf z = Σ_{(i, m, c) ∈ fin} c/(z − qᵢ)^m + Σ_{(k, c) ∈ inf} c z^k`, a sum of principal parts.

Elements of `K = ℚ(r, s)` are stored as four rationals and interpreted with *any* chosen square roots:
```lean
structure Z4 (A B : ℤ) where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
  deriving DecidableEq, Repr
```
`Z4.val r s x = x.a + x.b·r + x.c·s + x.d·(r·s)`.

Per case (identical text in every `Case<case>.lean`):
```lean
def DT : LP := trL t00 t01 t10 t11 D
def pfin (k l : ℕ) : List (ℕ × ℕ × K) := PFfinL.getD (k * V + l) []
def pinf (k l : ℕ) : List (ℕ × K) := PFinfL.getD (k * V + l) []
def iz : ℕ := pts.length - 1
def qv (r s : F) : List F := pts.map (Z4.val r s)
```
`qv r s` is the list of punctures in `F`, the last one being `0`. `DT` is `D` in the coordinates `v`.

## 3. The three main theorems (identical statements in all eight namespaces)

The hypotheses `hr : r ^ 2 = KA` and `hs : s ^ 2 = KB` are section variables of `curve` and `partial_fractions`
(and of the sanity theorems `curve_v`, `eul_ne_zero_at_2`, `integrand` in §4); `r s : F` are arbitrary.

```lean
theorem adjugate (x1 x2 : F) (h1 : x1 ≠ 0) (h2 : x2 ≠ 0) :
    lapMat V E x1 x2 * lmat V A x1 x2 = leval D x1 x2 • (1 : Matrix (Fin V) (Fin V) F)
```
**Theorem A.** `M(x)·A(x) = D(x)·I` for all `x₁, x₂ ≠ 0`.

```lean
theorem curve (z : F) (hz : ∀ q ∈ qv r s, z ≠ q) :
    leval D (xpar (qv r s) ex1 z) (xpar (qv r s) ex2 z) = 0
```
**Theorem B.** `D(x(z)) = 0` for every `z` that is not a puncture. This is the identity `P(x(z)) ≡ 0` of
Lemma `lem:param` in [E2] and [E3] (not the birationality part).

```lean
theorem partial_fractions (k l : Fin V) (z : F) (hz : ∀ q ∈ qv r s, z ≠ q) :
    leval (A k l) (xpar (qv r s) ex1 z) (xpar (qv r s) ex2 z) * dlogv (qv r s) ev1 z =
      leval (eul DT) (xpar (qv r s) ev1 z) (xpar (qv r s) ev2 z) *
        pfval (qv r s) ((pfin k l).map fun t => (t.1, t.2.1, Z4.val r s t.2.2))
          ((pinf k l).map fun t => (t.1, Z4.val r s t.2)) z
```
**Theorem C.** For every entry `(k, l)` and every `z` that is not a puncture,
`A_kl(x(z)) · v₁'/v₁(z) = (v₂∂_{v₂}D^T)(v(z)) · PF_kl(z)`. Divided by the denominator (see `integrand` below), this
says that `ρ_kl` *is* the explicit partial-fraction sum `PF_kl`: Lemma `lem:poles`(a) of [E2] and the first sentence
of the proof of Lemma `lem:poles` in [E3], for all `V²` entries.

**The roots `r, s` are arbitrary.** All three theorems hold for every `r, s ∈ F` with `r² = KA`, `s² = KB`. With
`F = ℂ` this covers the four embeddings of `K`, in particular the parametrisation and its conjugate under `τ`
([E2, Step 5], [E3, Step 5]): the principal parts of the conjugate integrand are the conjugate coefficients.

## 4. Sanity theorems (`Sanity<case>.lean`, added in the review)

These show that Theorems A–C are not vacuous and that the data fit together as the papers say. Identical in all eight
namespaces.

```lean
theorem D_ne_zero : leval D (2 : F) 3 ≠ 0
theorem green (x1 x2 : F) (h1 : x1 ≠ 0) (h2 : x2 ≠ 0) (hD : leval D x1 x2 ≠ 0) :
    (lapMat V E x1 x2)⁻¹ = (leval D x1 x2)⁻¹ • lmat V A x1 x2
```
`D` is not the zero polynomial (`D(2, 3) ≠ 0`). Without this, Theorem A would also hold with `A = D = 0`. With it,
`M(x)⁻¹ = A(x)/D(x)` wherever `D(x) ≠ 0` — the Green function used in the papers.

```lean
theorem T_det : t00 * t11 - t01 * t10 = 1
theorem x_eq_vT (z : F) (hz : ∀ q ∈ qv r s, z ≠ q) :
    xpar (qv r s) ex1 z = xpar (qv r s) ev1 z ^ t00 * xpar (qv r s) ev2 z ^ t10 ∧
    xpar (qv r s) ex2 z = xpar (qv r s) ev1 z ^ t01 * xpar (qv r s) ev2 z ^ t11
theorem curve_v (z : F) (hz : ∀ q ∈ qv r s, z ≠ q) :
    leval DT (xpar (qv r s) ev1 z) (xpar (qv r s) ev2 z) = 0
```
`T ∈ SL₂(ℤ)`, and the two exponent lists `ex` (coordinates `x`) and `ev` (coordinates `v`) describe the same map:
`x = v^T`. So Theorem C really uses `v(z)` for the same parametrisation as Theorem B, and `D^T(v(z)) = 0`.

```lean
theorem eul_ne_zero_at_2 :
    leval (eul DT) (xpar (qv r s) ev1 ((2 : ℚ) : F)) (xpar (qv r s) ev2 ((2 : ℚ) : F)) ≠ 0
theorem integrand (k l : Fin V) (z : F) (hz : ∀ q ∈ qv r s, z ≠ q)
    (hE : leval (eul DT) (xpar (qv r s) ev1 z) (xpar (qv r s) ev2 z) ≠ 0) :
    leval (A k l) (xpar (qv r s) ex1 z) (xpar (qv r s) ex2 z) * dlogv (qv r s) ev1 z /
        leval (eul DT) (xpar (qv r s) ev1 z) (xpar (qv r s) ev2 z) =
      pfval (qv r s) ((pfin k l).map fun t => (t.1, t.2.1, Z4.val r s t.2.2)) [] z
```
The denominator `v₂∂_{v₂}D^T(v(z))` is not identically zero along the curve, and where it is nonzero `ρ_kl = PF_kl`.

```lean
theorem pinf_nil (k l : ℕ) : pinf k l = []
theorem pfin_zero_simple (k l : ℕ) : ∀ t ∈ pfin k l, t.1 = iz → t.2.1 = 1
```
`PF_kl` has no polynomial part and at most a simple pole at `z = 0`. Hence `ρ_kl = O(1/z)` at `∞` and has a
simple pole at `0`, as stated in [E2, Lemma 11(a)].

## 5. What was checked outside Lean (review of 2026-11-24, independent Python code)

For each of the eight data files, parsed directly from the `.lean` source:
* `D = det M(x)` and `A = adj M(x)` at random rational points (exact arithmetic).
* The quotient graph is the stated lattice: vertex degrees, the number of faces per cell from Euler's formula,
  the triangles, chordless 4- and 6-cycles per cell and per vertex (e.g. 3⁴.6: 8 triangles and 1 hexagon per
  cell, 4 triangles at every vertex), and the conductances sit on the stated edges (3⁴.6: weight 4 exactly on
  the 6 edges lying in one triangle; [3.4².6; 3.6.3.6]₂: 3/5 exactly on edges between two squares; 4.6.12: 1/5
  exactly on edges in a square and a hexagon; 3³.4²: 3 on the edge in two squares).
* `D` agrees up to a constant with the Bloch determinants printed in [E3], section "The lattices and their train tracks" (factors −6, −15, 1, −1, −36).
* The punctures are exactly those of [E2, Step 1] and the table of exact train tracks in [E3], all on the unit circle, pairwise distinct;
  `deg v₁` is 8, 8, 6 resp. 4 and `T` is as in [E2, Step 2] and the table of proof data in [E3].

**[check]** These are checks of the data against the papers, not Lean proofs. A Lean proof that `E` is the
quotient graph of a given tiling would need a formal model of the tiling; we consider the combinatorial checks
above sufficient.

## 6. Not formalised

* `D = det M` (Lean proves `M·A = D·I` and `D ≠ 0`, which is what the residue formula uses).
* Birationality of `z ↦ x(z)`; the choice of `T`; the residue formula for the inner integral.
* The cycle `Γ`, the integers `k_q`, Lemma `lem:torus`, Lemma `lem:galois` (interval arithmetic).
* Lemma `lem:poles`(b): that the poles of `ρ_f` at `0` and `∞` cancel and `Σ c_{q,1} = 0` (an analytic
  integrability argument).
* The integration and Baker's theorem.
