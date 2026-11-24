import LeanResidy.Imports

/-!
# Beräkningsbara modeller av kommutativa ringar med sund tolkning

Allt som maskinräknas i projektet görs i små beräkningsbara datatyper (rationella tal, element i
ℚ(r, s) med r² = A, s² = B, polynom, rationella funktioner med givna nämnarfaktorer). Varje typ har
en tolkning `val` i en godtycklig kropp `F` av karakteristik 0, och vi bevisar att tolkningen
respekterar `+`, `*`, `-` och att testet `isZero` är sunt. En identitet som kärnan räknat ut till
`isZero … = true` (med `decide +kernel`) blir därmed en identitet i `F`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace LeanResidy

/-- En beräkningsbar "ringmodell". -/
class Comp (C : Type) where
  zero : C
  add : C → C → C
  mul : C → C → C
  neg : C → C
  ofQ : ℚ → C
  isZero : C → Bool

open LeanResidy.Comp

/-- `val` är en sund tolkning av modellen `C` i kroppen `F`. -/
structure Sound {C : Type} [Comp C] {F : Type} [Field F] (val : C → F) : Prop where
  zero : val Comp.zero = 0
  add : ∀ a b, val (Comp.add a b) = val a + val b
  mul : ∀ a b, val (Comp.mul a b) = val a * val b
  neg : ∀ a, val (Comp.neg a) = - val a
  ofQ : ∀ q : ℚ, val (Comp.ofQ q) = (q : F)
  isZero : ∀ a, Comp.isZero a = true → val a = 0

/-! ## Rationella tal -/

instance : Comp ℚ where
  zero := 0
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  ofQ := id
  isZero q := q == 0

theorem sound_rat (F : Type) [Field F] [CharZero F] : Sound (fun q : ℚ => (q : F)) where
  zero := by simp [Comp.zero]
  add a b := by simp [Comp.add]
  mul a b := by simp [Comp.mul]
  neg a := by simp [Comp.neg]
  ofQ q := rfl
  isZero a h := by
    simp only [Comp.isZero, beq_iff_eq] at h
    simp [h]

/-! ## Bikvadratiska kroppar ℚ(r, s), r² = A, s² = B -/

/-- `a + b·r + c·s + d·r·s`. -/
structure Z4 (A B : ℤ) where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
  deriving DecidableEq, Repr

instance (A B : ℤ) : Comp (Z4 A B) where
  zero := ⟨0, 0, 0, 0⟩
  add x y := ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩
  mul x y := ⟨x.a * y.a + A * x.b * y.b + B * x.c * y.c + A * B * x.d * y.d,
              x.a * y.b + x.b * y.a + B * (x.c * y.d + x.d * y.c),
              x.a * y.c + x.c * y.a + A * (x.b * y.d + x.d * y.b),
              x.a * y.d + x.d * y.a + x.b * y.c + x.c * y.b⟩
  neg x := ⟨-x.a, -x.b, -x.c, -x.d⟩
  ofQ q := ⟨q, 0, 0, 0⟩
  isZero x := x.a == 0 && x.b == 0 && x.c == 0 && x.d == 0

namespace Z4
variable {A B : ℤ} {F : Type} [Field F]

/-- Tolkningen `a + b r + c s + d r s` för valda kvadratrötter `r`, `s` i `F`. -/
def val (r s : F) (x : Z4 A B) : F := x.a + x.b * r + x.c * s + x.d * (r * s)

theorem sound [CharZero F] (r s : F) (hr : r ^ 2 = A) (hs : s ^ 2 = B) :
    Sound (val (A := A) (B := B) r s) where
  zero := by simp [val, Comp.zero]
  add x y := by simp [val, Comp.add]; ring
  mul x y := by
    simp only [val, Comp.mul]; push_cast
    linear_combination (-(x.b * y.b + x.d * y.d * s ^ 2 + (x.b * y.d + x.d * y.b) * s)) * hr +
      (-(x.c * y.c + x.d * y.d * (A : F) + (x.c * y.d + x.d * y.c) * r)) * hs
  neg x := by simp [val, Comp.neg]; ring
  ofQ q := by simp [val, Comp.ofQ]
  isZero x h := by
    simp only [Comp.isZero, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    simp [val, h1, h2, h3, h4]

/-- Konjugaten r ↦ −r, s ↦ −s. -/
def cr (x : Z4 A B) : Z4 A B := ⟨x.a, -x.b, x.c, -x.d⟩
def cs (x : Z4 A B) : Z4 A B := ⟨x.a, x.b, -x.c, -x.d⟩

/-- Normen (produkten av de fyra konjugaten), som ett element i modellen. -/
def norm (x : Z4 A B) : Z4 A B :=
  Comp.mul (Comp.mul x (cr x)) (Comp.mul (cs x) (cr (cs x)))

/-- Om normen är ett nollskilt rationellt tal är `x ≠ 0` (oavsett val av rötter). -/
theorem val_ne_zero [CharZero F] (r s : F) (hr : r ^ 2 = A) (hs : s ^ 2 = B) (x : Z4 A B)
    (h : (norm x).b = 0 ∧ (norm x).c = 0 ∧ (norm x).d = 0 ∧ (norm x).a ≠ 0) :
    val r s x ≠ 0 := by
  have S := sound r s hr hs
  intro h0
  have : val r s (norm x) = 0 := by
    simp only [norm, S.mul, h0, zero_mul]
  simp only [val, h.1, h.2.1, h.2.2.1] at this
  simp at this
  exact h.2.2.2 this

end Z4

/-! ## Polynom (täta koefficientlistor, lägsta grad först) -/

namespace P
variable {C : Type} [Comp C]

def add : List C → List C → List C
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => Comp.add a b :: add p q

def scale (c : C) (p : List C) : List C := p.map (Comp.mul c)

def mul : List C → List C → List C
  | [], _ => []
  | a :: p, q => add (scale a q) (Comp.zero :: mul p q)

def neg (p : List C) : List C := p.map Comp.neg

def pow (p : List C) : ℕ → List C
  | 0 => [Comp.ofQ 1]
  | n + 1 => mul p (pow p n)

def isZero (p : List C) : Bool := p.all Comp.isZero

variable {F : Type} [Field F]

/-- Hornerevaluering i `z`. -/
def val (v : C → F) (z : F) : List C → F
  | [] => 0
  | a :: p => v a + z * val v z p

variable {v : C → F} (S : Sound v) (z : F)
include S

theorem val_add (p q : List C) : val v z (add p q) = val v z p + val v z q := by
  induction p generalizing q with
  | nil => simp [add, val]
  | cons a p ih =>
    cases q with
    | nil => simp [add, val]
    | cons b q => simp [add, val, S.add, ih]; ring

theorem val_scale (c : C) (p : List C) : val v z (scale c p) = v c * val v z p := by
  induction p with
  | nil => simp [scale, val]
  | cons a p ih => simp only [scale, List.map, val, S.mul] at *; rw [ih]; ring

theorem val_mul (p q : List C) : val v z (mul p q) = val v z p * val v z q := by
  induction p with
  | nil => simp [mul, val]
  | cons a p ih => simp [mul, val, val_add S, val_scale S, S.zero, ih]; ring

theorem val_neg (p : List C) : val v z (neg p) = - val v z p := by
  induction p with
  | nil => simp [neg, val]
  | cons a p ih => simp only [neg, List.map, val, S.neg] at *; rw [ih]; ring

theorem val_pow (p : List C) (n : ℕ) : val v z (pow p n) = val v z p ^ n := by
  induction n with
  | zero => simp [pow, val, S.ofQ]
  | succ n ih => simp [pow, val_mul S, ih]; ring

theorem val_isZero (p : List C) (h : isZero p = true) : val v z p = 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [isZero, List.all_cons, Bool.and_eq_true] at h
    simp [val, S.isZero a h.1, ih h.2]

end P

/-! ## Rationella funktioner med nämnare ∏ (z − qᵢ)^{kᵢ} över en fix punktlista -/

/-- `num(z) / ∏ᵢ (z − ptsᵢ)^{kᵢ}`. -/
structure Fr (C : Type) (pts : List C) where
  num : List C
  k : List ℕ

namespace Fr
variable {C : Type} [Comp C]

def kadd : List ℕ → List ℕ → List ℕ
  | [], k => k
  | k, [] => k
  | a :: k, b :: k' => (a + b) :: kadd k k'

def kmax : List ℕ → List ℕ → List ℕ
  | [], k => k
  | k, [] => k
  | a :: k, b :: k' => max a b :: kmax k k'

def ksub : List ℕ → List ℕ → List ℕ
  | k, [] => k
  | [], _ => []
  | a :: k, b :: k' => (a - b) :: ksub k k'

/-- linjärfaktorn `z − q` -/
def lf (q : C) : List C := [Comp.neg q, Comp.ofQ 1]

/-- ∏ (z − ptsᵢ)^{kᵢ} som polynom -/
def fac : List C → List ℕ → List C
  | q :: ps, n :: ks => P.mul (P.pow (lf q) n) (fac ps ks)
  | _, _ => [Comp.ofQ 1]

variable {pts : List C}

instance : Comp (Fr C pts) where
  zero := ⟨[], []⟩
  add x y :=
    let k := kmax x.k y.k
    ⟨P.add (P.mul x.num (fac pts (ksub k x.k))) (P.mul y.num (fac pts (ksub k y.k))), k⟩
  mul x y := ⟨P.mul x.num y.num, kadd x.k y.k⟩
  neg x := ⟨P.neg x.num, x.k⟩
  ofQ q := ⟨[Comp.ofQ q], []⟩
  isZero x := P.isZero x.num

variable {F : Type} [Field F]

/-- nämnaren ∏ (z − v qᵢ)^{kᵢ} -/
def dval (v : C → F) (z : F) : List C → List ℕ → F
  | q :: ps, n :: ks => (z - v q) ^ n * dval v z ps ks
  | _, _ => 1

def val (v : C → F) (z : F) (x : Fr C pts) : F := P.val v z x.num / dval v z pts x.k

section
variable {v : C → F} (S : Sound v) (z : F)
include S

theorem val_lf (q : C) : P.val v z (lf q) = z - v q := by
  simp [lf, P.val, S.neg, S.ofQ]; ring

theorem val_fac (ps : List C) (ks : List ℕ) : P.val v z (fac ps ks) = dval v z ps ks := by
  induction ps generalizing ks with
  | nil => cases ks <;> simp [fac, dval, P.val, S.ofQ]
  | cons q ps ih =>
    cases ks with
    | nil => simp [fac, dval, P.val, S.ofQ]
    | cons n ks => simp [fac, dval, P.val_mul S, P.val_pow S, val_lf S, ih]
end

theorem dval_kadd (v : C → F) (z : F) (ps : List C) (k1 k2 : List ℕ) :
    dval v z ps (kadd k1 k2) = dval v z ps k1 * dval v z ps k2 := by
  induction ps generalizing k1 k2 with
  | nil => cases k1 <;> cases k2 <;> simp [kadd, dval]
  | cons q ps ih =>
    cases k1 with
    | nil => simp [kadd, dval]
    | cons a k1 =>
      cases k2 with
      | nil => simp [kadd, dval]
      | cons b k2 => simp [kadd, dval, ih, pow_add]; ring

theorem dval_ksub_self (v : C → F) (z : F) (ps : List C) (k : List ℕ) :
    dval v z ps (ksub k k) = 1 := by
  induction ps generalizing k with
  | nil => cases k <;> simp [ksub, dval]
  | cons q ps ih => cases k with
    | nil => simp [ksub, dval]
    | cons a k => simp [ksub, dval, ih]

theorem dval_kmax_left (v : C → F) (z : F) (ps : List C) (k1 k2 : List ℕ) :
    dval v z ps (kmax k1 k2) = dval v z ps k1 * dval v z ps (ksub (kmax k1 k2) k1) := by
  induction ps generalizing k1 k2 with
  | nil => cases k1 <;> cases k2 <;> simp [kmax, ksub, dval]
  | cons q ps ih =>
    cases k1 with
    | nil => cases k2 <;> simp [kmax, ksub, dval]
    | cons a k1 =>
      cases k2 with
      | nil => simp [kmax, ksub, dval, dval_ksub_self]
      | cons b k2 =>
        simp only [kmax, ksub, dval, ih]
        have : max a b = a + (max a b - a) := by omega
        rw [this, pow_add]; simp only [Nat.add_sub_cancel_left]; ring

theorem dval_kmax_right (v : C → F) (z : F) (ps : List C) (k1 k2 : List ℕ) :
    dval v z ps (kmax k1 k2) = dval v z ps k2 * dval v z ps (ksub (kmax k1 k2) k2) := by
  induction ps generalizing k1 k2 with
  | nil => cases k1 <;> cases k2 <;> simp [kmax, ksub, dval]
  | cons q ps ih =>
    cases k1 with
    | nil => cases k2 <;> simp [kmax, ksub, dval, dval_ksub_self]
    | cons a k1 =>
      cases k2 with
      | nil => simp [kmax, ksub, dval]
      | cons b k2 =>
        simp only [kmax, ksub, dval, ih]
        have : max a b = b + (max a b - b) := by omega
        rw [this, pow_add]; simp only [Nat.add_sub_cancel_left]; ring

theorem dval_ne_zero (v : C → F) (z : F) (ps : List C) (hz : ∀ q ∈ ps, z ≠ v q)
    (k : List ℕ) : dval v z ps k ≠ 0 := by
  induction ps generalizing k with
  | nil => cases k <;> simp [dval]
  | cons q ps ih =>
    cases k with
    | nil => simp [dval]
    | cons n k =>
      simp only [dval]
      refine mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr (hz q (by simp)))) ?_
      exact ih (fun q' hq' => hz q' (by simp [hq'])) k

theorem sound {v : C → F} (S : Sound v) (z : F) (hz : ∀ q ∈ pts, z ≠ v q) :
    Sound (val (pts := pts) v z) where
  zero := by simp [val, Comp.zero, P.val]
  add x y := by
    simp only [val, Comp.add]
    rw [P.val_add S, P.val_mul S, P.val_mul S, val_fac S, val_fac S]
    have hA := dval_kmax_left v z pts x.k y.k
    have hB := dval_kmax_right v z pts x.k y.k
    have h1 := dval_ne_zero v z pts hz x.k
    have h2 := dval_ne_zero v z pts hz y.k
    have h3 := dval_ne_zero v z pts hz (kmax x.k y.k)
    rw [div_add_div _ _ h1 h2, div_eq_div_iff h3 (mul_ne_zero h1 h2)]
    linear_combination (-(P.val v z x.num) * dval v z pts y.k) * hA +
      (-(P.val v z y.num) * dval v z pts x.k) * hB
  mul x y := by
    simp only [val, Comp.mul]
    rw [P.val_mul S, dval_kadd, div_mul_div_comm]
  neg x := by simp only [val, Comp.neg]; rw [P.val_neg S, neg_div]
  ofQ q := by simp [val, Comp.ofQ, P.val, S.ofQ, dval]
  isZero x h := by
    simp only [val, Comp.isZero] at *
    rw [P.val_isZero S z _ h, zero_div]

end Fr

/-! ## Laurentpolynom i två variabler: data `((i, j), c)` betyder `c · x₁^i · x₂^j` -/

abbrev LP := List ((ℤ × ℤ) × ℚ)

section Laurent
variable {C : Type} [Comp C]

def npow (x : C) : ℕ → C
  | 0 => Comp.ofQ 1
  | n + 1 => Comp.mul x (npow x n)

def zp (x xi : C) : ℤ → C
  | Int.ofNat n => npow x n
  | Int.negSucc n => npow xi (n + 1)

/-- beräkningsbar evaluering av ett Laurentpolynom, givet `x₁, x₁⁻¹, x₂, x₂⁻¹` i modellen -/
def lev (L : LP) (x1 x1i x2 x2i : C) : C :=
  L.foldr (fun t acc => Comp.add (Comp.mul (Comp.ofQ t.2) (Comp.mul (zp x1 x1i t.1.1)
    (zp x2 x2i t.1.2))) acc) Comp.zero

variable {F : Type} [Field F]

/-- matematisk evaluering -/
def leval (L : LP) (x1 x2 : F) : F := (L.map fun t => (t.2 : F) * x1 ^ t.1.1 * x2 ^ t.1.2).sum

variable {v : C → F} (S : Sound v)
include S

theorem val_npow (x : C) (n : ℕ) : v (npow x n) = v x ^ n := by
  induction n with
  | zero => simp [npow, S.ofQ]
  | succ n ih => simp [npow, S.mul, ih]; ring

theorem val_zp (x xi : C) (h : v xi = (v x)⁻¹) (n : ℤ) : v (zp x xi n) = v x ^ n := by
  cases n with
  | ofNat n => simp [zp, val_npow S]
  | negSucc n => simp [zp, val_npow S, h, zpow_negSucc, inv_pow]

theorem val_lev (L : LP) (x1 x1i x2 x2i : C) (h1 : v x1i = (v x1)⁻¹) (h2 : v x2i = (v x2)⁻¹) :
    v (lev L x1 x1i x2 x2i) = leval L (v x1) (v x2) := by
  induction L with
  | nil => simp [lev, leval, S.zero]
  | cons t L ih =>
    simp only [lev, List.foldr_cons] at *
    simp only [S.add, S.mul, S.ofQ, val_zp S _ _ h1, val_zp S _ _ h2, ih, leval, List.map_cons,
      List.sum_cons]
    ring

end Laurent

theorem leval_append {F : Type} [Field F] (L1 L2 : LP) (x1 x2 : F) :
    leval (L1 ++ L2) x1 x2 = leval L1 x1 x2 + leval L2 x1 x2 := by
  simp [leval]

end LeanResidy
