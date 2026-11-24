import LeanResidy.Lap

/-!
# Generiska kontroller: adjunktidentiteten, kurvidentiteten och partialbråken

Här definieras de booleska kontrollfunktionerna som kärnan räknar ut för varje fall, och de
generiska satser som översätter `kontroll = true` till identiteter i en godtycklig kropp.
-/

namespace LeanResidy
open LeanResidy.Comp
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {F : Type} [Field F]

/-! ## Summor i modellen -/

def sumC {C : Type} [Comp C] (l : List C) : C := l.foldr Comp.add Comp.zero

theorem lsum_range (n : ℕ) (f : ℕ → F) : ((List.range n).map f).sum = ∑ j : Fin n, f j := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Fin.sum_univ_castSucc]; simp

theorem val_sumC {C : Type} [Comp C] {v : C → F} (S : Sound v) (l : List C) :
    v (sumC l) = (l.map v).sum := by
  induction l with
  | nil => simp [sumC, S.zero]
  | cons a l ih => simp only [sumC, List.foldr_cons] at *; simp [S.add, ih]

/-! ## Adjunktidentiteten M(x)·A(x) = D(x)·I i två variabler -/

/-- modellen för rationella funktioner i x₂ med nämnare x₂^k -/
abbrev Q2 := Fr ℚ [(0 : ℚ)]
/-- modellen för rationella funktioner i x₁ med koefficienter i `Q2`, nämnare x₁^k -/
abbrev Q3 := Fr Q2 [(Comp.zero : Q2)]

def bX2 : Q2 := ⟨[0, 1], []⟩
def bX2i : Q2 := ⟨[1], [1]⟩
def bX1 : Q3 := ⟨[Comp.zero, Comp.ofQ 1], []⟩
def bX1i : Q3 := ⟨[Comp.ofQ 1], [1]⟩

def bev (L : LP) : Q3 := lev L bX1 bX1i (⟨[bX2], []⟩ : Q3) (⟨[bX2i], []⟩ : Q3)

/-- kontrollen av `(M·A)ᵢₖ = D·δᵢₖ` för alla `i, k` -/
def adjCheck (V : ℕ) (E : List Edge) (A : ℕ → ℕ → LP) (D : LP) : Bool :=
  (List.range V).all fun i => (List.range V).all fun k =>
    Comp.isZero (Comp.add (sumC ((List.range V).map fun j =>
        (Comp.mul (bev (lapL E i j)) (bev (A j k)) : Q3)))
      (Comp.neg (if i = k then bev D else Comp.zero)))

section
variable [CharZero F]

def bval2 (x2 : F) : Q2 → F := Fr.val (fun q : ℚ => (q : F)) x2
def bval3 (x1 x2 : F) : Q3 → F := Fr.val (bval2 x2) x1

theorem sound_b (x1 x2 : F) (h1 : x1 ≠ 0) (h2 : x2 ≠ 0) : Sound (bval3 x1 x2) := by
  have S2 : Sound (bval2 x2) := Fr.sound (sound_rat F) x2 (by simpa using h2)
  refine Fr.sound S2 x1 ?_
  intro q hq
  simp only [List.mem_singleton] at hq
  subst hq
  rw [S2.zero]; exact h1

theorem bev_val (x1 x2 : F) (h1 : x1 ≠ 0) (h2 : x2 ≠ 0) (L : LP) :
    bval3 x1 x2 (bev L) = leval L x1 x2 := by
  have S := sound_b x1 x2 h1 h2
  have S2 : Sound (bval2 x2) := Fr.sound (sound_rat F) x2 (by simpa using h2)
  have e1 : bval3 x1 x2 bX1 = x1 := by
    simp [bval3, bX1, Fr.val, P.val, S2.zero, S2.ofQ, Fr.dval]
  have e1i : bval3 x1 x2 bX1i = x1⁻¹ := by
    simp [bval3, bX1i, Fr.val, P.val, S2.ofQ, Fr.dval, S2.zero]
  have e2 : bval3 x1 x2 (⟨[bX2], []⟩ : Q3) = x2 := by
    simp [bval3, Fr.val, P.val, Fr.dval, bval2, bX2]
  have e2i : bval3 x1 x2 (⟨[bX2i], []⟩ : Q3) = x2⁻¹ := by
    simp [bval3, Fr.val, P.val, Fr.dval, bval2, bX2i]
  unfold bev
  rw [val_lev S L _ _ _ _ (by rw [e1i, e1]) (by rw [e2i, e2]), e1, e2]

/-- Laurentpolynom-matrisen som matris över `F`. -/
def lmat (V : ℕ) (A : ℕ → ℕ → LP) (x1 x2 : F) : Matrix (Fin V) (Fin V) F :=
  fun i j => leval (A i j) x1 x2

theorem adj_of_check (V : ℕ) (E : List Edge) (A : ℕ → ℕ → LP) (D : LP)
    (h : adjCheck V E A D = true) (x1 x2 : F) (h1 : x1 ≠ 0) (h2 : x2 ≠ 0) :
    lapMat V E x1 x2 * lmat V A x1 x2 = leval D x1 x2 • (1 : Matrix (Fin V) (Fin V) F) := by
  have S := sound_b x1 x2 h1 h2
  ext i k
  simp only [adjCheck, List.all_eq_true, List.mem_range] at h
  have hik := S.isZero _ (h i i.2 k k.2)
  rw [S.add, S.neg, val_sumC S, List.map_map] at hik
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
  have : (∑ j : Fin V, lapMat V E x1 x2 i j * lmat V A x1 x2 j k) =
      (((List.range V).map ((bval3 x1 x2) ∘ fun j =>
        (Comp.mul (bev (lapL E i j)) (bev (A j k)) : Q3))).sum) := by
    rw [lsum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [S.mul, bev_val x1 x2 h1 h2, lapMat_eq, lmat]
  rw [this]
  by_cases hk : i = k
  · subst hk; simp [bev_val x1 x2 h1 h2] at hik ⊢; linear_combination hik
  · have hk' : (i : ℕ) ≠ k := fun e => hk (Fin.ext e)
    simp [hk, hk', S.zero] at hik ⊢; linear_combination hik
end

/-! ## Identiteter i z över ℚ(r, s) -/

section Z
variable {A B : ℤ}

/-- `c/(z − ptsᵢ)^m` som element i modellen -/
def kvec (i m : ℕ) : List ℕ := List.replicate i 0 ++ [m]

def single {pts : List (Z4 A B)} (i m : ℕ) (c : Z4 A B) : Fr (Z4 A B) pts := ⟨[c], kvec i m⟩

/-- `c·z^k` -/
def zmon {pts : List (Z4 A B)} (k : ℕ) (c : Z4 A B) : Fr (Z4 A B) pts :=
  ⟨List.replicate k Comp.zero ++ [c], []⟩

/-- partialbråket som element i modellen -/
def pfF {pts : List (Z4 A B)} (fin : List (ℕ × ℕ × Z4 A B)) (inf : List (ℕ × Z4 A B)) :
    Fr (Z4 A B) pts :=
  Comp.add (sumC (fin.map fun t => single t.1 t.2.1 t.2.2)) (sumC (inf.map fun t => zmon t.1 t.2))

/-- Σᵢ eᵢ/(z − ptsᵢ) i modellen -/
def dlogF {pts : List (Z4 A B)} (es : List ℤ) : Fr (Z4 A B) pts :=
  sumC ((List.range es.length).map fun i => single i 1 (Comp.ofQ (es.getD i 0)))

/-- matematiskt: partialbråket `Σ c/(z − qᵢ)^m + Σ c z^k` -/
def pfval (qs : List F) (fin : List (ℕ × ℕ × F)) (inf : List (ℕ × F)) (z : F) : F :=
  (fin.map fun t => t.2.2 / (z - qs.getD t.1 0) ^ t.2.1).sum + (inf.map fun t => t.2 * z ^ t.1).sum

/-- matematiskt: logaritmiska derivatan `Σ eᵢ/(z − qᵢ)` av `∏ (z − qᵢ)^{eᵢ}` -/
def dlogv (qs : List F) (es : List ℤ) (z : F) : F :=
  ((List.range es.length).map fun i => (es.getD i 0 : F) / (z - qs.getD i 0)).sum

variable [CharZero F] {pts : List (Z4 A B)} (r s : F) (hr : r ^ 2 = A) (hs : s ^ 2 = B) (z : F)
  (hz : ∀ q ∈ pts, z ≠ Z4.val r s q)

/-- tolkningen av modellen `Fr (Z4 A B) pts` -/
def zval : Fr (Z4 A B) pts → F := Fr.val (Z4.val r s) z

include hr hs hz

theorem zsound : Sound (zval (pts := pts) r s z) := Fr.sound (Z4.sound r s hr hs) z hz

omit hr hs hz in
theorem dval_kvec (v : Z4 A B → F) (ps : List (Z4 A B)) (i m : ℕ) (hi : i < ps.length) :
    Fr.dval v z ps (kvec i m) = (z - (ps.map v).getD i 0) ^ m := by
  induction i generalizing ps with
  | zero => cases ps with
    | nil => simp at hi
    | cons q ps => simp [kvec, Fr.dval]
  | succ i ih => cases ps with
    | nil => simp at hi
    | cons q ps =>
      have := ih ps (by simpa using hi)
      simp only [kvec, List.replicate_succ, List.cons_append, Fr.dval, pow_zero, one_mul] at this ⊢
      rw [this]; simp

theorem val_single (i m : ℕ) (c : Z4 A B) (hi : i < pts.length) :
    zval r s z (single (pts := pts) i m c) = Z4.val r s c / (z - (pts.map (Z4.val r s)).getD i 0) ^ m := by
  simp [zval, single, Fr.val, P.val, dval_kvec z _ pts i m hi]

theorem val_zmon (k : ℕ) (c : Z4 A B) :
    zval r s z (zmon (pts := pts) k c) = Z4.val r s c * z ^ k := by
  have S := Z4.sound r s hr hs
  simp only [zval, zmon, Fr.val]
  have : Fr.dval (Z4.val r s) z pts [] = 1 := by cases pts <;> simp [Fr.dval]
  rw [this, div_one]
  induction k with
  | zero => simp [P.val]
  | succ k ih => simp [List.replicate_succ, P.val, S.zero, ih]; ring

theorem val_pfF (fin : List (ℕ × ℕ × Z4 A B)) (inf : List (ℕ × Z4 A B))
    (hfin : fin.all (fun t => decide (t.1 < pts.length)) = true) :
    zval r s z (pfF (pts := pts) fin inf) =
      pfval (pts.map (Z4.val r s)) (fin.map fun t => (t.1, t.2.1, Z4.val r s t.2.2))
        (inf.map fun t => (t.1, Z4.val r s t.2)) z := by
  have S := zsound r s hr hs z hz
  simp only [pfF, S.add, val_sumC S, List.map_map, pfval]
  congr 1
  · simp only [List.all_eq_true, decide_eq_true_eq] at hfin
    apply congrArg List.sum
    apply List.map_congr_left
    intro t ht
    simp [val_single r s hr hs z hz _ _ _ (hfin t ht)]
  · apply congrArg List.sum
    apply List.map_congr_left
    intro t _
    simp [val_zmon r s hr hs z hz]

theorem val_dlogF (es : List ℤ) (hl : es.length ≤ pts.length) :
    zval r s z (dlogF (pts := pts) es) = dlogv (pts.map (Z4.val r s)) es z := by
  have S := zsound r s hr hs z hz
  have S4 := Z4.sound r s hr hs
  simp only [dlogF, val_sumC S, List.map_map, dlogv]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  rw [Function.comp_apply, val_single r s hr hs z hz _ _ _ (by omega), S4.ofQ, pow_one, Rat.cast_intCast]

theorem val_frPar_inv (es : List ℤ) :
    zval r s z (frPar pts (es.map (- ·))) = (zval r s z (frPar pts es))⁻¹ := by
  have S4 := Z4.sound r s hr hs
  simp only [zval, Fr.val, frPar, Fr.val_fac S4, inv_div]
  congr 2 <;> simp [posE, negE, Function.comp_def]

end Z

/-! ## Monomiellt koordinatbyte och Eulers operator -/

/-- `D ↦ D^T`, exponenten `(a, b) ↦ (t₀₀a + t₀₁b, t₁₀a + t₁₁b)` (som `resmaskin.tr`) -/
def trL (t00 t01 t10 t11 : ℤ) (L : LP) : LP :=
  L.map fun t => ((t00 * t.1.1 + t01 * t.1.2, t10 * t.1.1 + t11 * t.1.2), t.2)

/-- Eulers operator `v₂ ∂/∂v₂` på ett Laurentpolynom -/
def eul (L : LP) : LP := L.map fun t => (t.1, t.2 * t.1.2)

theorem leval_trL (t00 t01 t10 t11 : ℤ) (L : LP) (v1 v2 : F) (h1 : v1 ≠ 0) (h2 : v2 ≠ 0) :
    leval (trL t00 t01 t10 t11 L) v1 v2 =
      leval L (v1 ^ t00 * v2 ^ t10) (v1 ^ t01 * v2 ^ t11) := by
  induction L with
  | nil => simp [trL, leval]
  | cons t L ih =>
    simp only [trL, leval, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    congr 1
    rw [mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul,
      zpow_add₀ h1, zpow_add₀ h2]
    ring

end LeanResidy
