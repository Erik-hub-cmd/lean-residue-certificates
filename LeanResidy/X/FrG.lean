import LeanResidy.X.Kron

/-!
# Rationella funktioner med givna nämnarfaktorer över en godtycklig modell

`FrG C dl`: element `num / ∏ⱼ dlⱼ^{kⱼ}` där `dl` är en fast lista av element i `C` (t.ex. polynom
i parametrarna). Samma konstruktion som `Fr` i `Basic.lean`, men nämnarfaktorerna är godtyckliga
element i `C` i stället för linjärfaktorer `z − q`. Tolkningen är sund så snart alla `dlⱼ` tolkas
som nollskilda.

För `C = PK` finns en (okontrollerad) invers: för ett element vars täljare har samma packade värde
som en nämnarfaktor, eller som är en konstant. Den används bara i kontrollpunkterna, där kärnan
ändå kontrollerar `w · w⁻¹ = 1` (`invOK`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace LeanResidy
namespace X
open LeanResidy.Comp

structure FrG (C : Type) (dl : List C) where
  num : C
  k : List ℕ

namespace FrG
variable {C : Type} [Comp C]

def npowC (x : C) : ℕ → C
  | 0 => Comp.ofQ 1
  | n + 1 => Comp.mul x (npowC x n)

/-- `∏ dlⱼ^{kⱼ}` i `C` -/
def facC : List C → List ℕ → C
  | q :: ps, n :: ks => if n = 0 then facC ps ks else Comp.mul (npowC q n) (facC ps ks)
  | _, _ => Comp.ofQ 1

/-- `x · ∏ dlⱼ^{eⱼ}`, utan multiplikation när alla `eⱼ = 0` -/
def mulFac (dl : List C) (x : C) (e : List ℕ) : C :=
  if e.all (· == 0) then x else Comp.mul x (facC dl e)

variable {dl : List C}

instance : Comp (FrG C dl) where
  zero := ⟨Comp.zero, []⟩
  add x y :=
    let k := Fr.kmax x.k y.k
    ⟨Comp.add (mulFac dl x.num (Fr.ksub k x.k)) (mulFac dl y.num (Fr.ksub k y.k)), k⟩
  mul x y := ⟨Comp.mul x.num y.num, Fr.kadd x.k y.k⟩
  neg x := ⟨Comp.neg x.num, x.k⟩
  ofQ q := ⟨Comp.ofQ q, []⟩
  isZero x := Comp.isZero x.num

variable {F : Type} [Field F]

/-- nämnaren `∏ v(dlⱼ)^{kⱼ}` -/
def dvalG (v : C → F) : List C → List ℕ → F
  | q :: ps, n :: ks => v q ^ n * dvalG v ps ks
  | _, _ => 1

def val (v : C → F) (x : FrG C dl) : F := v x.num / dvalG v dl x.k

section
variable {v : C → F} (S : Sound v)
include S

theorem val_npowC (x : C) (n : ℕ) : v (npowC x n) = v x ^ n := by
  induction n with
  | zero => simp [npowC, S.ofQ]
  | succ n ih => simp [npowC, S.mul, ih, pow_succ]; ring

theorem val_facC (ps : List C) (ks : List ℕ) : v (facC ps ks) = dvalG v ps ks := by
  induction ps generalizing ks with
  | nil => cases ks <;> simp [facC, dvalG, S.ofQ]
  | cons q ps ih =>
    cases ks with
    | nil => simp [facC, dvalG, S.ofQ]
    | cons n ks =>
      simp only [facC, dvalG]
      split_ifs with h
      · subst h; simp [ih]
      · rw [S.mul, val_npowC S, ih]

theorem dvalG_zeros (ps : List C) (e : List ℕ) (h : e.all (· == 0) = true) : dvalG v ps e = 1 := by
  induction ps generalizing e with
  | nil => cases e <;> simp [dvalG]
  | cons q ps ih =>
    cases e with
    | nil => simp [dvalG]
    | cons n e =>
      simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
      simp [dvalG, h.1, ih e h.2]

theorem val_mulFac (x : C) (e : List ℕ) : v (mulFac dl x e) = v x * dvalG v dl e := by
  simp only [mulFac]
  split_ifs with h
  · rw [dvalG_zeros S dl e h, mul_one]
  · rw [S.mul, val_facC S]
end

theorem dvalG_kadd (v : C → F) (ps : List C) (k1 k2 : List ℕ) :
    dvalG v ps (Fr.kadd k1 k2) = dvalG v ps k1 * dvalG v ps k2 := by
  induction ps generalizing k1 k2 with
  | nil => cases k1 <;> cases k2 <;> simp [Fr.kadd, dvalG]
  | cons q ps ih =>
    cases k1 with
    | nil => simp [Fr.kadd, dvalG]
    | cons a k1 =>
      cases k2 with
      | nil => simp [Fr.kadd, dvalG]
      | cons b k2 => simp [Fr.kadd, dvalG, ih, pow_add]; ring

theorem dvalG_ksub_self (v : C → F) (ps : List C) (k : List ℕ) : dvalG v ps (Fr.ksub k k) = 1 := by
  induction ps generalizing k with
  | nil => cases k <;> simp [Fr.ksub, dvalG]
  | cons q ps ih => cases k with
    | nil => simp [Fr.ksub, dvalG]
    | cons a k => simp [Fr.ksub, dvalG, ih]

theorem dvalG_kmax_left (v : C → F) (ps : List C) (k1 k2 : List ℕ) :
    dvalG v ps (Fr.kmax k1 k2) = dvalG v ps k1 * dvalG v ps (Fr.ksub (Fr.kmax k1 k2) k1) := by
  induction ps generalizing k1 k2 with
  | nil => cases k1 <;> cases k2 <;> simp [Fr.kmax, Fr.ksub, dvalG]
  | cons q ps ih =>
    cases k1 with
    | nil => cases k2 <;> simp [Fr.kmax, Fr.ksub, dvalG]
    | cons a k1 =>
      cases k2 with
      | nil => simp [Fr.kmax, Fr.ksub, dvalG, dvalG_ksub_self]
      | cons b k2 =>
        simp only [Fr.kmax, Fr.ksub, dvalG, ih]
        have : max a b = a + (max a b - a) := by omega
        rw [this, pow_add]; simp only [Nat.add_sub_cancel_left]; ring

theorem dvalG_kmax_right (v : C → F) (ps : List C) (k1 k2 : List ℕ) :
    dvalG v ps (Fr.kmax k1 k2) = dvalG v ps k2 * dvalG v ps (Fr.ksub (Fr.kmax k1 k2) k2) := by
  induction ps generalizing k1 k2 with
  | nil => cases k1 <;> cases k2 <;> simp [Fr.kmax, Fr.ksub, dvalG]
  | cons q ps ih =>
    cases k1 with
    | nil => cases k2 <;> simp [Fr.kmax, Fr.ksub, dvalG, dvalG_ksub_self]
    | cons a k1 =>
      cases k2 with
      | nil => simp [Fr.kmax, Fr.ksub, dvalG]
      | cons b k2 =>
        simp only [Fr.kmax, Fr.ksub, dvalG, ih]
        have : max a b = b + (max a b - b) := by omega
        rw [this, pow_add]; simp only [Nat.add_sub_cancel_left]; ring

theorem dvalG_ne_zero (v : C → F) (ps : List C) (hz : ∀ q ∈ ps, v q ≠ 0) (k : List ℕ) :
    dvalG v ps k ≠ 0 := by
  induction ps generalizing k with
  | nil => cases k <;> simp [dvalG]
  | cons q ps ih =>
    cases k with
    | nil => simp [dvalG]
    | cons n k =>
      simp only [dvalG]
      exact mul_ne_zero (pow_ne_zero _ (hz q (by simp))) (ih (fun q' hq' => hz q' (by simp [hq'])) k)

theorem sound {v : C → F} (S : Sound v) (hz : ∀ q ∈ dl, v q ≠ 0) : Sound (val (dl := dl) v) where
  zero := by simp [val, Comp.zero, S.zero]
  add x y := by
    simp only [val, Comp.add]
    rw [S.add, val_mulFac S, val_mulFac S]
    have hA := dvalG_kmax_left v dl x.k y.k
    have hB := dvalG_kmax_right v dl x.k y.k
    have h1 := dvalG_ne_zero v dl hz x.k
    have h2 := dvalG_ne_zero v dl hz y.k
    have h3 := dvalG_ne_zero v dl hz (Fr.kmax x.k y.k)
    rw [div_add_div _ _ h1 h2, div_eq_div_iff h3 (mul_ne_zero h1 h2)]
    linear_combination (-(v x.num) * dvalG v dl y.k) * hA + (-(v y.num) * dvalG v dl x.k) * hB
  mul x y := by
    simp only [val, Comp.mul]
    rw [S.mul, dvalG_kadd, div_mul_div_comm]
  neg x := by simp only [val, Comp.neg]; rw [S.neg, neg_div]
  ofQ q := by simp [val, Comp.ofQ, S.ofQ, dvalG]
  isZero x h := by
    simp only [val, Comp.isZero] at *
    rw [S.isZero _ h, zero_div]

end FrG

/-! ## Okontrollerad invers i `FrG (PK …) dl` -/

namespace PK
variable {A B : ℤ} {Kb S : ℕ}

/-- alla fyra packade tal är `< 2^(Kb-1)` i belopp (heuristik för "konstant", okontrollerad) -/
def small (N : I4) : Bool :=
  N.a.natAbs < 2 ^ (Kb - 1) && N.b.natAbs < 2 ^ (Kb - 1) && N.c.natAbs < 2 ^ (Kb - 1) &&
    N.d.natAbs < 2 ^ (Kb - 1)

/-- `x` har de packade värdena `N` -/
def sameN (x : PK A B Kb S) (N : I4) : Bool :=
  x.N.a == N.a && x.N.b == N.b && x.N.c == N.c && x.N.d == N.d

/-- konstanten `x.N / x.den` (meningsfull bara om `x` är konstant) som `Z4` -/
def toZ4 (x : PK A B Kb S) : Z4 A B :=
  ⟨(x.N.a : ℚ) / x.den, (x.N.b : ℚ) / x.den, (x.N.c : ℚ) / x.den, (x.N.d : ℚ) / x.den⟩

/-- `Z4`-konstant som element -/
def ofZ4 (z : Z4 A B) : PK A B Kb S :=
  add (add (ofQ z.a) (mul (ofQ z.b) (const ⟨0, 1, 0, 0⟩ 1 Nat.one_pos)))
    (add (mul (ofQ z.c) (const ⟨0, 0, 1, 0⟩ 1 Nat.one_pos))
      (mul (ofQ z.d) (const ⟨0, 0, 0, 1⟩ 1 Nat.one_pos)))

end PK

def findDl {A B : ℤ} {Kb S : ℕ} (dl : List (PK A B Kb S)) (N : I4) : Option ℕ :=
  (List.range dl.length).find? fun j => PK.sameN (dl.getD j PK.zero) N

instance {A B : ℤ} {Kb S : ℕ} {dl : List (PK A B Kb S)} : CInv (FrG (PK A B Kb S) dl) where
  inv x :=
    if x.num.da == 0 && PK.small (Kb := Kb) x.num.N then
      -- konstant täljare
      ⟨Comp.mul (PK.ofZ4 (Z4.inv (PK.toZ4 x.num))) (FrG.facC dl x.k), []⟩
    else match findDl dl x.num.N with
      | some j => ⟨Comp.mul (PK.ofQ x.num.den) (FrG.facC dl x.k), kvec j 1⟩
      | none => ⟨Comp.zero, []⟩

end X
end LeanResidy
