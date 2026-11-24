import LeanResidy.X.Basic

/-!
# Generiska residykontroller över en godtycklig koefficientmodell `K`

Samma tre kontroller som i `LeanResidy.Generic`/`Points` och fallfilerna (adjunkten, kurvan,
partialbråken), men

* koefficienterna (kantvikter, adjunkten, determinanten, punkteringar, residyer) ligger i en godtycklig
  beräkningsbar modell `K` med sund tolkning `vK : K → F` (t.ex. `Z8` = ℚ(r, s, t), eller rationella
  funktioner i en viktparameter), och
* inverserna i kontrollpunkterna kontrolleras genom multiplikation (`invOK`), så att inget om
  modellens invers behöver bevisas.

Beviset görs **en gång** här för en godtycklig datamängd `c : Case K`; fallfilerna innehåller bara data
och kärnans räkningar.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace LeanResidy
namespace X
open LeanResidy.Comp

variable {F : Type} [Field F]

/-- Laurentpolynom med koefficienter i `K`: `((i, j), c)` betyder `c · x₁^i · x₂^j` -/
abbrev LPK (K : Type) := List ((ℤ × ℤ) × K)
/-- kant `(i, j, n₁, n₂, w)` med vikt `w ∈ K` -/
abbrev EdgeK (K : Type) := ℕ × ℕ × ℤ × ℤ × K

section Lev
variable {K C : Type} [Comp K] [Comp C]

/-- beräkningsbar evaluering i modellen `C`, med koefficienterna inbäddade via `emb` -/
def levK (emb : K → C) (L : LPK K) (x1 x1i x2 x2i : C) : C :=
  L.foldr (fun t acc => Comp.add (Comp.mul (emb t.2) (Comp.mul (zp x1 x1i t.1.1)
    (zp x2 x2i t.1.2))) acc) Comp.zero

/-- matematisk evaluering -/
def levalK (vK : K → F) (L : LPK K) (x1 x2 : F) : F :=
  (L.map fun t => vK t.2 * x1 ^ t.1.1 * x2 ^ t.1.2).sum

theorem levalK_append (vK : K → F) (L1 L2 : LPK K) (x1 x2 : F) :
    levalK vK (L1 ++ L2) x1 x2 = levalK vK L1 x1 x2 + levalK vK L2 x1 x2 := by
  simp [levalK]

theorem val_levK {v : C → F} (S : Sound v) (vK : K → F) (emb : K → C) (hemb : ∀ k, v (emb k) = vK k)
    (L : LPK K) (x1 x1i x2 x2i : C) (h1 : v x1i = (v x1)⁻¹) (h2 : v x2i = (v x2)⁻¹) :
    v (levK emb L x1 x1i x2 x2i) = levalK vK L (v x1) (v x2) := by
  induction L with
  | nil => simp [levK, levalK, S.zero]
  | cons t L ih =>
    simp only [levK, List.foldr_cons] at *
    simp only [S.add, S.mul, hemb, val_zp S _ _ h1, val_zp S _ _ h2, ih, levalK, List.map_cons,
      List.sum_cons]
    ring

end Lev

/-! ## Laplacianen med vikter i `K` -/

section Lap
variable {K : Type} [Comp K]

/-- bidraget från en kant till post `(i, j)` (samma konvention som `resmaskin.lap`) -/
def edgeCK (vK : K → F) (x1 x2 : F) (i j : ℕ) (e : EdgeK K) : F :=
  let a := e.1; let b := e.2.1; let n1 := e.2.2.1; let n2 := e.2.2.2.1; let w : F := vK e.2.2.2.2
  (if i = a ∧ j = a then w else 0) + (if i = b ∧ j = b then w else 0)
    - (if i = a ∧ j = b then w * (x1 ^ n1 * x2 ^ n2) else 0)
    - (if i = b ∧ j = a then w * (x1 ^ n1 * x2 ^ n2)⁻¹ else 0)

/-- Laplacianen `M(x₁, x₂)` med vikterna `vK w` -/
def lapMatK (vK : K → F) (V : ℕ) (E : List (EdgeK K)) (x1 x2 : F) : Matrix (Fin V) (Fin V) F :=
  fun i j => (E.map (edgeCK vK x1 x2 i j)).sum

def edgeLK (i j : ℕ) (e : EdgeK K) : LPK K :=
  let a := e.1; let b := e.2.1; let n1 := e.2.2.1; let n2 := e.2.2.2.1; let w := e.2.2.2.2
  (if i = a ∧ j = a then [((0, 0), w)] else []) ++ (if i = b ∧ j = b then [((0, 0), w)] else [])
    ++ (if i = a ∧ j = b then [((n1, n2), Comp.neg w)] else [])
    ++ (if i = b ∧ j = a then [((-n1, -n2), Comp.neg w)] else [])

def lapLK (E : List (EdgeK K)) (i j : ℕ) : LPK K := E.flatMap (edgeLK i j)

variable {vK : K → F} (S : Sound vK)
include S

theorem edgeCK_eq (x1 x2 : F) (i j : ℕ) (e : EdgeK K) :
    edgeCK vK x1 x2 i j e = levalK vK (edgeLK i j e) x1 x2 := by
  simp only [edgeCK, edgeLK, levalK_append]
  split_ifs <;> simp [levalK, zpow_neg, mul_inv, S.neg] <;> ring

theorem lapMatK_eq (V : ℕ) (E : List (EdgeK K)) (x1 x2 : F) (i j : Fin V) :
    lapMatK vK V E x1 x2 i j = levalK vK (lapLK E i j) x1 x2 := by
  simp only [lapMatK, lapLK]
  induction E with
  | nil => simp [levalK]
  | cons e E ih => simp [List.flatMap_cons, levalK_append, edgeCK_eq S, ih]

end Lap

/-! ## Adjunktidentiteten -/

section Adj
variable {K : Type} [Comp K]

abbrev Q2K (K : Type) [Comp K] := Fr K [(Comp.zero : K)]
abbrev Q3K (K : Type) [Comp K] := Fr (Q2K K) [(Comp.zero : Q2K K)]

def cX2 : Q2K K := ⟨[Comp.zero, Comp.ofQ 1], []⟩
def cX2i : Q2K K := ⟨[Comp.ofQ 1], [1]⟩
def cX1 : Q3K K := ⟨[Comp.zero, Comp.ofQ 1], []⟩
def cX1i : Q3K K := ⟨[Comp.ofQ 1], [1]⟩
def emb3 (k : K) : Q3K K := ⟨[⟨[k], []⟩], []⟩

def bevK (L : LPK K) : Q3K K :=
  levK emb3 L cX1 cX1i (⟨[cX2], []⟩ : Q3K K) (⟨[cX2i], []⟩ : Q3K K)

/-- rad `i` av kontrollen `(M·A)ᵢₖ = D·δᵢₖ` -/
def adjEntK (V : ℕ) (E : List (EdgeK K)) (A : ℕ → ℕ → LPK K) (D : LPK K) (i k : ℕ) : Bool :=
  Comp.isZero (Comp.add (sumC ((List.range V).map fun j =>
      (Comp.mul (bevK (lapLK E i j)) (bevK (A j k)) : Q3K K)))
    (Comp.neg (if i = k then bevK D else Comp.zero)))

def adjRowK (V : ℕ) (E : List (EdgeK K)) (A : ℕ → ℕ → LPK K) (D : LPK K) (i : ℕ) : Bool :=
  (List.range V).all fun k => adjEntK V E A D i k

def cval2 (vK : K → F) (x2 : F) : Q2K K → F := Fr.val vK x2
def cval3 (vK : K → F) (x1 x2 : F) : Q3K K → F := Fr.val (cval2 vK x2) x1

variable {vK : K → F} (S : Sound vK)
include S

theorem sound_c2 (x2 : F) (h2 : x2 ≠ 0) : Sound (cval2 vK x2) :=
  Fr.sound S x2 (by intro q hq; simp only [List.mem_singleton] at hq; subst hq; rw [S.zero]; exact h2)

theorem sound_c (x1 x2 : F) (h1 : x1 ≠ 0) (h2 : x2 ≠ 0) : Sound (cval3 vK x1 x2) := by
  have S2 := sound_c2 S x2 h2
  refine Fr.sound S2 x1 ?_
  intro q hq
  simp only [List.mem_singleton] at hq
  subst hq
  rw [S2.zero]; exact h1

theorem bevK_val (x1 x2 : F) (h1 : x1 ≠ 0) (h2 : x2 ≠ 0) (L : LPK K) :
    cval3 vK x1 x2 (bevK L) = levalK vK L x1 x2 := by
  have S3 := sound_c S x1 x2 h1 h2
  have S2 := sound_c2 S x2 h2
  have e1 : cval3 vK x1 x2 cX1 = x1 := by
    simp [cval3, cX1, Fr.val, P.val, S2.zero, S2.ofQ, Fr.dval]
  have e1i : cval3 vK x1 x2 cX1i = x1⁻¹ := by
    simp [cval3, cX1i, Fr.val, P.val, S2.ofQ, Fr.dval, S2.zero]
  have e2 : cval3 vK x1 x2 (⟨[cX2], []⟩ : Q3K K) = x2 := by
    simp [cval3, Fr.val, P.val, Fr.dval, cval2, cX2, S.zero, S.ofQ]
  have e2i : cval3 vK x1 x2 (⟨[cX2i], []⟩ : Q3K K) = x2⁻¹ := by
    simp [cval3, Fr.val, P.val, Fr.dval, cval2, cX2i, S.zero, S.ofQ]
  have he : ∀ k, cval3 vK x1 x2 (emb3 k) = vK k := by
    intro k; simp [cval3, emb3, Fr.val, P.val, Fr.dval, cval2]
  unfold bevK
  rw [val_levK S3 vK emb3 he L _ _ _ _ (by rw [e1i, e1]) (by rw [e2i, e2]), e1, e2]

/-- Laurentpolynom-matrisen som matris över `F`. -/
def lmatK (vK : K → F) (V : ℕ) (A : ℕ → ℕ → LPK K) (x1 x2 : F) : Matrix (Fin V) (Fin V) F :=
  fun i j => levalK vK (A i j) x1 x2

theorem adj_of_checkK (V : ℕ) (E : List (EdgeK K)) (A : ℕ → ℕ → LPK K) (D : LPK K)
    (h : ∀ i < V, adjRowK V E A D i = true) (x1 x2 : F) (h1 : x1 ≠ 0) (h2 : x2 ≠ 0) :
    lapMatK vK V E x1 x2 * lmatK vK V A x1 x2 = levalK vK D x1 x2 • (1 : Matrix (Fin V) (Fin V) F) := by
  have S3 := sound_c S x1 x2 h1 h2
  ext i k
  have hi := h i i.2
  simp only [adjRowK, adjEntK, List.all_eq_true, List.mem_range] at hi
  have hik := S3.isZero _ (hi k k.2)
  rw [S3.add, S3.neg, val_sumC S3, List.map_map] at hik
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
  have : (∑ j : Fin V, lapMatK vK V E x1 x2 i j * lmatK vK V A x1 x2 j k) =
      (((List.range V).map ((cval3 vK x1 x2) ∘ fun j =>
        (Comp.mul (bevK (lapLK E i j)) (bevK (A j k)) : Q3K K))).sum) := by
    rw [lsum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [S3.mul, bevK_val S x1 x2 h1 h2, lapMatK_eq S, lmatK]
  rw [this]
  by_cases hk : i = k
  · subst hk; simp [bevK_val S x1 x2 h1 h2] at hik ⊢; linear_combination hik
  · have hk' : (i : ℕ) ≠ k := fun e => hk (Fin.ext e)
    simp [hk, hk', S3.zero] at hik ⊢; linear_combination hik

end Adj

/-! ## Kurvan: exakt i rationella funktioner av `z` över `K` -/

section Curve
variable {K : Type} [Comp K]

def embZ {pts : List K} (k : K) : Fr K pts := ⟨[k], []⟩

def curveCheckK (D : LPK K) (pts : List K) (ex1 ex2 : List ℤ) : Bool :=
  Comp.isZero (levK embZ D (frPar pts ex1) (frPar pts (ex1.map (- ·)))
    (frPar pts ex2) (frPar pts (ex2.map (- ·))) : Fr K pts)

variable {vK : K → F} (S : Sound vK)
include S

theorem val_frPar_invK (pts : List K) (z : F) (es : List ℤ) :
    Fr.val vK z (frPar pts (es.map (- ·))) = (Fr.val vK z (frPar pts es))⁻¹ := by
  simp only [Fr.val, frPar, Fr.val_fac S, inv_div]
  congr 2 <;> simp [posE, negE, Function.comp_def]

theorem curve_of_checkK (D : LPK K) (pts : List K) (ex1 ex2 : List ℤ)
    (h : curveCheckK D pts ex1 ex2 = true) (z : F) (hz : ∀ q ∈ pts.map vK, z ≠ q) :
    levalK vK D (xpar (pts.map vK) ex1 z) (xpar (pts.map vK) ex2 z) = 0 := by
  have hz2 : ∀ q ∈ pts, z ≠ vK q := fun q hq => hz _ (List.mem_map_of_mem hq)
  have SZ : Sound (Fr.val (pts := pts) vK z) := Fr.sound S z hz2
  have h0 := SZ.isZero _ h
  have he : ∀ k, Fr.val (pts := pts) vK z (embZ k) = vK k := by
    intro k; cases pts <;> simp [embZ, Fr.val, P.val, Fr.dval]
  have e1 : Fr.val vK z (frPar pts ex1) = xpar (pts.map vK) ex1 z := val_frPar S z ex1
  have e2 : Fr.val vK z (frPar pts ex2) = xpar (pts.map vK) ex2 z := val_frPar S z ex2
  rw [val_levK SZ vK embZ he _ _ _ _ _ (by rw [val_frPar_invK S]) (by rw [val_frPar_invK S]),
    e1, e2] at h0
  exact h0

end Curve

/-! ## Monomsummor med koefficienter i `K` -/

section MonK
variable {K : Type} [Comp K]

def slevK (L : LPK K) (x1 x1i x2 x2i : List (Mon K)) : List (Mon K) :=
  L.flatMap fun t => smul [(t.2, [])] (smul (szp x1 x1i t.1.1) (szp x2 x2i t.1.2))

variable {vK : K → F} (S : Sound vK) (qs : List F) (z : F) (hz : ∀ q ∈ qs, z ≠ q)
include S hz

theorem sval_levK (L : LPK K) (x1 x1i x2 x2i : List (Mon K))
    (h1 : sval vK qs z x1i = (sval vK qs z x1)⁻¹) (h2 : sval vK qs z x2i = (sval vK qs z x2)⁻¹) :
    sval vK qs z (slevK L x1 x1i x2 x2i) = levalK vK L (sval vK qs z x1) (sval vK qs z x2) := by
  induction L with
  | nil => simp [slevK, sval, levalK]
  | cons t L ih =>
    simp only [slevK, List.flatMap_cons] at ih ⊢
    rw [sval_append S qs z, ih, sval_mul S qs z hz, sval_mul S qs z hz, sval_zp S qs z hz _ _ h1,
      sval_zp S qs z hz _ _ h2]
    simp [sval, pe_nil, levalK]
    ring

end MonK

/-! ## Koordinatbyte och Eulers operator med koefficienter i `K` -/

section TrK
variable {K : Type} [Comp K]

/-- `D ↦ D^T`, exponenten `(a, b) ↦ (t₀₀a + t₀₁b, t₁₀a + t₁₁b)` (som `resmaskin.tr`) -/
def trLK (t00 t01 t10 t11 : ℤ) (L : LPK K) : LPK K :=
  L.map fun t => ((t00 * t.1.1 + t01 * t.1.2, t10 * t.1.1 + t11 * t.1.2), t.2)

/-- Eulers operator `v₂ ∂/∂v₂`: `((a, b), c) ↦ ((a, b), b·c)` -/
def eulK (L : LPK K) : LPK K := L.map fun t => (t.1, Comp.mul (Comp.ofQ (t.1.2 : ℚ)) t.2)

theorem levalK_trLK (vK : K → F) (t00 t01 t10 t11 : ℤ) (L : LPK K) (v1 v2 : F) (h1 : v1 ≠ 0)
    (h2 : v2 ≠ 0) :
    levalK vK (trLK t00 t01 t10 t11 L) v1 v2 =
      levalK vK L (v1 ^ t00 * v2 ^ t10) (v1 ^ t01 * v2 ^ t11) := by
  induction L with
  | nil => simp [trLK, levalK]
  | cons t L ih =>
    simp only [trLK, levalK, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    congr 1
    rw [mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul,
      zpow_add₀ h1, zpow_add₀ h2]
    ring

end TrK

end X
end LeanResidy
