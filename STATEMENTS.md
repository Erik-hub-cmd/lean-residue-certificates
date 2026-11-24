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

[3².6²; 3.6.3.6] of [E3] (field `ℚ(i, √2, √3)` of degree 8) and 3.12² and 4.8² with a variable conductance
([E3], section "General conductances") are in the extension `LeanResidy.X`, §7. Not included: the families with two
independent conductance ratios ([3².6²; 3.6.3.6] and [3.4.3.12; 3.12²] with all conductances).

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

## 7. Extension `LeanResidy.X`: three further cases (added and reviewed 2026-11-24)

`LeanResidy/X/` adds the three cases that §1 lists as not included in the first version. The files of §1–§6 are
unchanged; `X/` reuses `Basic.lean` and `Points.lean`.

| namespace | lattice | paper | conductances | coefficients | `V` | entries |
|---|---|---|---|---|---|---|
| `X.Cf2a` | [3².6²; 3.6.3.6] | [E3] | 1 | `ℚ(r, s, t)`, `r² = −1, s² = 2, t² = 3` | 3 | 9 |
| `X.C3122t` | 3.12² | [E3], Theorem `thm:3122t` | 1 on triangle edges, `u` on dodecagon–dodecagon edges, **every** `u ≠ 0, −3/2` | `ℚ(r, s)(u)`, `r² = −3, s² = −1` | 6 | 36 |
| `X.C488u` | 4.8² | [E3], Theorem `thm:488t` | `1 − c` on square edges, `2c` on octagon–octagon edges, `c = (u + u⁻¹)/2`, **every** `u` outside a finite list | `ℚ(r, s)(u)`, `r² = −1, s² = −2` | 4 | 16 |

In [E3] the parameter of 3.12² is called `t`; for 4.8², `u = e^{iθ_t}` with `cos θ_t = t/(2 + t)`, and the
conductances `(1 − c, 2c)` are proportional to `(1, t)` (proof of Theorem `thm:488t`).

### 7.1 Definitions

The coefficients now lie in a computable model `K` with an interpretation `vK : K → F` that respects the operations
(`Sound vK`, the same notion as in `Basic.lean`). The definitions of §2 are repeated with coefficients in `K`:

```lean
abbrev LPK (K : Type) := List ((ℤ × ℤ) × K)
/-- kant `(i, j, n₁, n₂, w)` med vikt `w ∈ K` -/
abbrev EdgeK (K : Type) := ℕ × ℕ × ℤ × ℤ × K
def levalK (vK : K → F) (L : LPK K) (x1 x2 : F) : F :=
  (L.map fun t => vK t.2 * x1 ^ t.1.1 * x2 ^ t.1.2).sum
abbrev EdgeK (K : Type) := ℕ × ℕ × ℤ × ℤ × K
def edgeCK (vK : K → F) (x1 x2 : F) (i j : ℕ) (e : EdgeK K) : F :=
  let a := e.1; let b := e.2.1; let n1 := e.2.2.1; let n2 := e.2.2.2.1; let w : F := vK e.2.2.2.2
  (if i = a ∧ j = a then w else 0) + (if i = b ∧ j = b then w else 0)
    - (if i = a ∧ j = b then w * (x1 ^ n1 * x2 ^ n2) else 0)
    - (if i = b ∧ j = a then w * (x1 ^ n1 * x2 ^ n2)⁻¹ else 0)
def lapMatK (vK : K → F) (V : ℕ) (E : List (EdgeK K)) (x1 x2 : F) : Matrix (Fin V) (Fin V) F :=
  fun i j => (E.map (edgeCK vK x1 x2 i j)).sum
def lmatK (vK : K → F) (V : ℕ) (A : ℕ → ℕ → LPK K) (x1 x2 : F) : Matrix (Fin V) (Fin V) F :=
  fun i j => levalK vK (A i j) x1 x2
def trLK (t00 t01 t10 t11 : ℤ) (L : LPK K) : LPK K :=
  L.map fun t => ((t00 * t.1.1 + t01 * t.1.2, t10 * t.1.1 + t11 * t.1.2), t.2)
def eulK (L : LPK K) : LPK K := L.map fun t => (t.1, Comp.mul (Comp.ofQ (t.1.2 : ℚ)) t.2)
```
These are `leval`, `edgeC`, `lapMat`, `lmat`, `trL`, `eul` of §2 with `(t.2 : F)` replaced by `vK t.2`. `xpar`,
`dlogv` and `pfval` are the definitions of §2 (unchanged). Per case, `data : Case K` holds the data; `data.A k l`,
`data.DT`, `data.pfin`, `data.pinf`, `data.iz` are as in §2, and the punctures in `F` are
```lean
def qv (vK : K → F) (c : Case K) : List F := c.pts.map vK
```

The models and their interpretations:
```lean
def val (v : C → F) (t : F) (p : Quad C a) : F := v p.x + v p.y * t
abbrev Z8 (A B : ℤ) (c : ℚ) := Quad (Z4 A B) (⟨c, 0, 0, 0⟩ : Z4 A B)
def Z8.val {A B : ℤ} {c : ℚ} {F : Type} [Field F] (r s t : F) : Z8 A B c → F :=
  Quad.val (Z4.val r s) t
def val (v : C → F) (z : F) (x : Fr C pts) : F := P.val v z x.num / dval v z pts x.k
```
`Quad C a` stores `x + y·t` with `t² = a`; `Z8` is `ℚ(r, s)(t)`. `Fr C pts` stores a rational function
`num(u) / ∏ (u − ptsᵢ)^{kᵢ}` (numerator as a coefficient list, evaluated by Horner's rule `P.val`). The three
interpretations:
```lean
def vK : K → F := Z8.val r s t
def vK : K → F := Fr.val (Z4.val r s) u
def vK : K → F := Fr.val (Z4.val r s) u
abbrev tpts : List (Z4 (-3) (-1)) := [(⟨(0 : ℚ), 0, 0, 0⟩ : Z4 (-3) (-1)), (⟨(-3/2 : ℚ), 0, 0, 0⟩ : Z4 (-3) (-1))]
```
For 4.8², `tpts` is the list `0, ±1, ±i, ±c, ±ic` for `c = 2, …, 17` (69 points in `ℚ(i, √−2)`; the points
`c ≥ 2` are needed because the punctures `±u, ±iu` move with `u` and must avoid the check points `z = 2, …, 16`).

### 7.2 The main theorems

Hypotheses (section variables): for `Cf2a`, `hr : r ^ 2 = ((-1 : ℤ) : F)`, `hs : s ^ 2 = ((2 : ℤ) : F)`,
`ht : t ^ 2 = ((3 : ℚ) : F)`; for `C3122t`, `hr : r ^ 2 = ((-3 : ℤ) : F)`, `hs : s ^ 2 = ((-1 : ℤ) : F)`,
`hu : ∀ p ∈ tpts, u ≠ Z4.val r s p`; for `C488u`, `hr : r ^ 2 = ((-1 : ℤ) : F)`, `hs : s ^ 2 = ((-2 : ℤ) : F)` and
the same `hu`. Statements for `Cf2a` (for the other two, replace `vK r s t` by `vK r s u`; the text is otherwise
identical):

```lean
theorem adjugate (x1 x2 : F) (h1 : x1 ≠ 0) (h2 : x2 ≠ 0) :
    lapMatK (vK r s t) data.V data.E x1 x2 * lmatK (vK r s t) data.V data.A x1 x2 =
      levalK (vK r s t) data.D x1 x2 • (1 : Matrix (Fin data.V) (Fin data.V) F)
theorem curve_ok : data.curveCheck = true
theorem partial_fractions (k l : Fin data.V) (z : F) (hz : ∀ q ∈ qv (vK r s t) data, z ≠ q) :
    levalK (vK r s t) (data.A k l) (xpar (qv (vK r s t) data) data.ex1 z)
        (xpar (qv (vK r s t) data) data.ex2 z) * dlogv (qv (vK r s t) data) data.ev1 z =
      levalK (vK r s t) (eulK data.DT) (xpar (qv (vK r s t) data) data.ev1 z)
          (xpar (qv (vK r s t) data) data.ev2 z) *
        pfval (qv (vK r s t) data) ((data.pfin k l).map fun t' => (t'.1, t'.2.1, vK r s t t'.2.2))
          ((data.pinf k l).map fun t' => (t'.1, vK r s t t'.2)) z
```
These are Theorems A, B, C of §3. For `Cf2a` they hold for **all eight** choices of `r, s, t` (all Galois
conjugates of the parametrisation over `ℚ(i, √2, √3)`, as used by Lemmas `lem:mob` and `lem:perm` of [E3]). For
`C3122t` and `C488u` they hold **identically in the conductance parameter `u`** (outside `tpts`). For 3.12², [E3]
verifies the partial-fraction identity at 16 values of `t` and extends by polynomiality; Lean proves it for all `t`
directly. For 4.8², this is the symbolic computation in `u` of step (1) of the proof of Theorem `thm:488t`.
(4.8²'s Theorem B is proved by the point method too, `curve_gen_pts`; the statement is the same.)

**[check]** The hypothesis `hu` is a finite list of excluded values. It holds for every `t > 0` (3.12²) and for
every `u` on the unit circle other than `±1, ±i` (4.8², `hu_unit` below), which covers `u = e^{iθ_t}`,
`θ_t ∈ (0, π/2)`.

### 7.3 Sanity theorems (`X/Sanity<case>.lean`, written in the review)

The theorems of §4, for each of the three namespaces (`T_det`, `x_eq_vT`, `curve_v`, `green`, `integrand`,
`pinf_nil`, `pfin_zero_simple`, `D_ne_zero`, `eul_ne_zero_at_2`), now with the parameter. In addition, `weights`
and `D_eq` tie the data to the paper directly in Lean.

```lean
theorem weights : data.E.map (fun e => (e.1, e.2.1, vK r s u e.2.2.2.2)) =
    [(0, 4, 1), (0, 3, u), (0, 2, 1), (1, 2, u), (1, 5, 1), (1, 3, 1), (2, 4, 1), (4, 5, u), (3, 5, 1)]
theorem weights : data.E.map (fun e => (e.1, e.2.1, e.2.2.1, e.2.2.2.1, vK r s u e.2.2.2.2)) =
    [(0, 1, 0, 0, 1 - (u + u⁻¹) / 2), (1, 2, 0, 0, 1 - (u + u⁻¹) / 2), (2, 3, 0, 0, 1 - (u + u⁻¹) / 2),
      (3, 0, 0, 0, 1 - (u + u⁻¹) / 2), (0, 2, 1, 0, 2 * ((u + u⁻¹) / 2)), (1, 3, 0, 1, 2 * ((u + u⁻¹) / 2))]
```
The conductances sit where [E3] says: for 3.12², `u` exactly on the three edges not in a triangle (the triangles are
`0, 2, 4` and `1, 3, 5`); for 4.8², `1 − c` on the square `0, 1, 2, 3` and `2c` on the octagon–octagon edges `0 → 2`
in cell `(1, 0)` and `1 → 3` in cell `(0, 1)` (as in `lat.py`). For `Cf2a` all six conductances are `1`.

```lean
theorem D_eq (x1 x2 : F) (h1 : x1 ≠ 0) (h2 : x2 ≠ 0) :
    levalK (vK r s t) data.D x1 x2 =
      -(x1 ^ 2 * x2 ^ 2 + 10 * x1 ^ 2 * x2 + x1 ^ 2 + 6 * x1 * x2 ^ 2 - 36 * x1 * x2 + 6 * x1 + x2 ^ 2 +
        10 * x2 + 1) / (x1 * x2)
theorem D_eq (x1 x2 : F) (h1 : x1 ≠ 0) (h2 : x2 ≠ 0) :
    levalK (vK r s u) data.D x1 x2 =
      -3 * u ^ 2 * (2 * u + 3) * (x1 + x1⁻¹ + x2 + x2⁻¹ + x1 * x2⁻¹ + x1⁻¹ * x2 - 6)
theorem D_eq (x1 x2 : F) (h1 : x1 ≠ 0) (h2 : x2 ≠ 0) :
    let c := (u + u⁻¹) / 2
    let a := 1 - c
    let b := 2 * c
    let W := 2 * a ^ 2 * b * (2 * a + b)
    let Dd := a ^ 2 * b ^ 2
    levalK (vK r s u) data.D x1 x2 =
      (2 * W + 2 * W + 4 * Dd) - W * (x1 + x1⁻¹) - W * (x2 + x2⁻¹) - Dd * (x1 + x1⁻¹) * (x2 + x2⁻¹)
```
`D` is, explicitly, the Bloch determinant of [E3]: for [3².6²; 3.6.3.6] the polynomial printed in section "The
lattices and their train tracks" (with sign −1); for 3.12², `−3u²(2u + 3)·P_△` as in Proposition
`prop:weights`(a) with `(w₀, w₁) = (1, u)`; for 4.8², `P_{W,D}` of Proposition `prop:weights`(b) with
`(a, b) = (1 − c, 2c)`.

```lean
theorem D_ne_zero : levalK (vK r s u) data.D (-1) (-1) ≠ 0
theorem eul_ne_zero_at_2 :
    levalK (vK r s u) (eulK data.DT) (xpar (qv (vK r s u) data) data.ev1 ((2 : ℚ) : F))
      (xpar (qv (vK r s u) data) data.ev2 ((2 : ℚ) : F)) ≠ 0
theorem eul_ne_zero_at_2 (hQ : (u - 4 * r) * (u ^ 2 + (-32/17 + 8/17 * r) * u - 4 * r) ≠ 0) :
    levalK (vK r s u) (eulK data.DT) (xpar (qv (vK r s u) data) data.ev1 ((2 : ℚ) : F))
      (xpar (qv (vK r s u) data) data.ev2 ((2 : ℚ) : F)) ≠ 0
```
`D ≢ 0` and the denominator of the integrand is not identically zero along the curve, **for every allowed value of
the parameter** (not only for one). For 4.8² the denominator at `z = 2` vanishes also at the three roots of an
explicit cubic `Q(u)` (moduli 4, ≈1.53, ≈2.62), which is therefore a hypothesis; `hQ_unit` shows it holds on the
unit circle.

```lean
theorem hu_unit (s : ℂ) (u : ℂ) (h1 : Complex.normSq u = 1) (hp1 : u ≠ 1) (hm1 : u ≠ -1) (hpi : u ≠ I)
    (hmi : u ≠ -I) : ∀ p ∈ tpts, u ≠ Z4.val I s p
theorem hQ_unit (u : ℂ) (h1 : Complex.normSq u = 1) :
    (u - 4 * I) * (u ^ 2 + (-32/17 + 8/17 * I) * u - 4 * I) ≠ 0
```
In `ℂ` with `r = i`: every `u` with `|u| = 1`, `u ≠ ±1, ±i`, satisfies the hypothesis `hu` of the main theorems
and the hypothesis of `eul_ne_zero_at_2`. (`X/Sanity.lean`, by the author of the code, shows the hypotheses at one
point each: `r = i, s = √2, t = √3`; `u = 1`; `u = (3 + 4i)/5`.)

### 7.4 Checked outside Lean (independent Python code, parsing the `.lean` data files)

* `D = det M(x)` **exactly** (symbolically in `x` and in the parameter), and `A = adj M(x)`, for all three cases.
* The punctures and their exponents are exactly those of eq. `xz` of [E3] with the tracks of the table of exact
  train tracks (`[3².6²; 3.6.3.6]`: `(1,0;1)`, `(1,0;ζ⁴)`, `(0,1;ζ¹⁷)`, `(0,1;ζ²³)`, `ζ = e^{iπ/12}`; 3.12²: those of
  3.6.3.6; 4.8²: `(1,0;1)`, `(1,0;u)`, `(0,1;−i)`, `(0,1;−iu)`); `T` as in the table of proof data.
* Theorems B and C evaluated numerically at a random `z` (3.12² at `t = 7/3`, 4.8² at `u = e^{0.7i}`): agreement to
  `10⁻¹³`.

### 7.5 Not formalised (in addition to §6)

For the weighted cases: the analytic arguments of Theorems `thm:3122t` and `thm:488t` (polynomiality in `t` of
`s(t)R`, the extension of the certified cycle data from `t = 1` to an interval, real-analyticity and the identity
theorem in `t`). For [3².6²; 3.6.3.6]: Lemma `lem:mob` (the Möbius maps `m_g`) and Lemma `lem:perm`. The two-parameter
families ([3².6²; 3.6.3.6] and [3.4.3.12; 3.12²] with all conductances) are not included: one point check already
needs more than 11 GB in the kernel with this method.
