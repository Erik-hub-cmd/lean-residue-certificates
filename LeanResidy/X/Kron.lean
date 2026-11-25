import LeanResidy.X.Basic

/-!
# Kronecker-packade polynom i två parametrar

Modellen `PK A B Kb S` är polynom i två parametrar `a`, `b` med koefficienter i `ℤ[r, s]`
(`r² = A`, `s² = B`) delade med ett positivt heltal `den`. Kärnan räknar **bara** med de packade
värdena: polynomet `Σ cᵢⱼ aⁱ bʲ` lagras som de fyra heltalen `Σ cᵢⱼ · Bb^(i + S·j)` (en komponent per
basvektor `1, r, s, rs`), där `Bb = 2^Kb`. Addition och multiplikation av polynom blir då några
få multiplikationer av stora heltal (GMP i kärnan).

Polynomet självt finns med som ett "spöke" `P` (en termlista) tillsammans med ett bevis `h` att de
packade talen, ℓ¹-gränsen `β` och gradgränsen `da` i `a` stämmer med `P`. Kärnan behöver aldrig räkna
ut `P` eller `h` (de projiceras aldrig fram i `isZero`), men tolkningen `val` och sundhetsbeviset
använder dem.

`isZero` kräver att alla fyra packade tal är 0, att `2β < Bb` och att `da < S`. Då är varje
koefficient (efter sammanslagning av lika monom) ett heltal med belopp `< Bb/2`, så de packade talen
bestämmer koefficienterna entydigt (Kroneckersubstitution, `kron_zero`), och polynomet är noll.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace LeanResidy
namespace X
open LeanResidy.Comp

/-- `a + b·r + c·s + d·r·s` med heltalskoefficienter -/
@[ext] structure I4 where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ

namespace I4

def zero : I4 := ⟨0, 0, 0, 0⟩
def add (x y : I4) : I4 := ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩
def smul (n : ℤ) (x : I4) : I4 := ⟨n * x.a, n * x.b, n * x.c, n * x.d⟩
def neg (x : I4) : I4 := ⟨-x.a, -x.b, -x.c, -x.d⟩
/-- samma formel som `Z4`-multiplikationen -/
def mul (A B : ℤ) (x y : I4) : I4 :=
  ⟨x.a * y.a + A * x.b * y.b + B * x.c * y.c + A * B * x.d * y.d,
   x.a * y.b + x.b * y.a + B * (x.c * y.d + x.d * y.c),
   x.a * y.c + x.c * y.a + A * (x.b * y.d + x.d * y.b),
   x.a * y.d + x.d * y.a + x.b * y.c + x.c * y.b⟩
/-- ℓ¹-normen av koefficienterna -/
def l1 (x : I4) : ℕ := x.a.natAbs + x.b.natAbs + x.c.natAbs + x.d.natAbs
def isZ (x : I4) : Bool := x.a == 0 && x.b == 0 && x.c == 0 && x.d == 0

variable {F : Type} [Field F]
def val (r s : F) (x : I4) : F := x.a + x.b * r + x.c * s + x.d * (r * s)

theorem val_mul (A B : ℤ) (r s : F) (hr : r ^ 2 = A) (hs : s ^ 2 = B) (x y : I4) :
    val r s (mul A B x y) = val r s x * val r s y := by
  simp only [val, mul]; push_cast
  linear_combination (-(x.b * y.b + x.d * y.d * s ^ 2 + (x.b * y.d + x.d * y.b) * s : F)) * hr +
    (-(x.c * y.c + x.d * y.d * (A : F) + (x.c * y.d + x.d * y.c) * r)) * hs

/-- `κ` med `‖x·y‖₁ ≤ κ ‖x‖₁ ‖y‖₁` -/
def kappa (A B : ℤ) : ℕ := 1 + A.natAbs + B.natAbs + A.natAbs * B.natAbs

theorem l1_mul (A B : ℤ) (x y : I4) : (mul A B x y).l1 ≤ kappa A B * x.l1 * y.l1 := by
  have key : ((mul A B x y).l1 : ℤ) ≤ (kappa A B : ℤ) * x.l1 * y.l1 := by
    simp only [l1, mul, kappa, Nat.cast_add, Nat.cast_mul, Int.natCast_natAbs]
    have t1 : ∀ p q u v : ℤ, |p + q + u + v| ≤ |p| + |q| + |u| + |v| := fun p q u v => by
      calc |p + q + u + v| ≤ |p + q + u| + |v| := abs_add_le _ _
        _ ≤ |p + q| + |u| + |v| := by gcongr; exact abs_add_le _ _
        _ ≤ |p| + |q| + |u| + |v| := by gcongr; exact abs_add_le _ _
    have e1 := t1 (x.a * y.a) (A * x.b * y.b) (B * x.c * y.c) (A * B * x.d * y.d)
    have e2 := t1 (x.a * y.b) (x.b * y.a) (B * (x.c * y.d)) (B * (x.d * y.c))
    have e3 := t1 (x.a * y.c) (x.c * y.a) (A * (x.b * y.d)) (A * (x.d * y.b))
    have e4 := t1 (x.a * y.d) (x.d * y.a) (x.b * y.c) (x.c * y.b)
    simp only [abs_mul] at e1 e2 e3 e4
    have r2 : x.a * y.b + x.b * y.a + B * (x.c * y.d + x.d * y.c) =
      x.a * y.b + x.b * y.a + B * (x.c * y.d) + B * (x.d * y.c) := by ring
    have r3 : x.a * y.c + x.c * y.a + A * (x.b * y.d + x.d * y.b) =
      x.a * y.c + x.c * y.a + A * (x.b * y.d) + A * (x.d * y.b) := by ring
    rw [r2, r3]
    have hA := abs_nonneg A; have hB := abs_nonneg B
    simp only [Nat.cast_one]
    have hT : (1 + |A| + |B| + |A| * |B|) * (|x.a| + |x.b| + |x.c| + |x.d|) * (|y.a| + |y.b| + |y.c| + |y.d|) -
        ((|x.a| * |y.a| + |A| * |x.b| * |y.b| + |B| * |x.c| * |y.c| + |A| * |B| * |x.d| * |y.d|) +
         (|x.a| * |y.b| + |x.b| * |y.a| + |B| * (|x.c| * |y.d|) + |B| * (|x.d| * |y.c|)) +
         (|x.a| * |y.c| + |x.c| * |y.a| + |A| * (|x.b| * |y.d|) + |A| * (|x.d| * |y.b|)) +
         (|x.a| * |y.d| + |x.d| * |y.a| + |x.b| * |y.c| + |x.c| * |y.b|)) =
        (|A| + |B| + |A| * |B|) * (|x.a| * |y.a| + |x.a| * |y.b| + |x.b| * |y.a| + |x.a| * |y.c| +
          |x.c| * |y.a| + |x.a| * |y.d| + |x.d| * |y.a| + |x.b| * |y.c| + |x.c| * |y.b|) +
        (1 + |B| + |A| * |B|) * (|x.b| * |y.b| + |x.b| * |y.d| + |x.d| * |y.b|) +
        (1 + |A| + |A| * |B|) * (|x.c| * |y.c| + |x.c| * |y.d| + |x.d| * |y.c|) +
        (1 + |A| + |B|) * (|x.d| * |y.d|) := by ring
    have hT0 : 0 ≤ (|A| + |B| + |A| * |B|) * (|x.a| * |y.a| + |x.a| * |y.b| + |x.b| * |y.a| + |x.a| * |y.c| +
          |x.c| * |y.a| + |x.a| * |y.d| + |x.d| * |y.a| + |x.b| * |y.c| + |x.c| * |y.b|) +
        (1 + |B| + |A| * |B|) * (|x.b| * |y.b| + |x.b| * |y.d| + |x.d| * |y.b|) +
        (1 + |A| + |A| * |B|) * (|x.c| * |y.c| + |x.c| * |y.d| + |x.d| * |y.c|) +
        (1 + |A| + |B|) * (|x.d| * |y.d|) := by positivity
    linarith
  exact_mod_cast key

end I4

/-! ## Spökpolynomet och de packade talen -/

/-- termlista `((i, j), c)` = `c · aⁱ · bʲ` -/
abbrev GP := List ((ℕ × ℕ) × I4)

/-- positionen för `aⁱ bʲ` i packningen -/
def gpos (S : ℕ) (e : ℕ × ℕ) : ℕ := e.1 + S * e.2

/-- packat värde av en komponent -/
def pkc (Bb S : ℕ) (f : I4 → ℤ) (P : GP) : ℤ := (P.map fun t => f t.2 * ((Bb ^ gpos S t.1 : ℕ) : ℤ)).sum

def pkI (Bb S : ℕ) (P : GP) : I4 := ⟨pkc Bb S I4.a P, pkc Bb S I4.b P, pkc Bb S I4.c P, pkc Bb S I4.d P⟩

def gl1 (P : GP) : ℕ := (P.map fun t => t.2.l1).sum
def gscale (n : ℤ) (P : GP) : GP := P.map fun t => (t.1, I4.smul n t.2)
def gneg (P : GP) : GP := P.map fun t => (t.1, I4.neg t.2)
def gmul (A B : ℤ) (P Q : GP) : GP :=
  P.flatMap fun t => Q.map fun u => ((t.1.1 + u.1.1, t.1.2 + u.1.2), I4.mul A B t.2 u.2)

section Ghost
variable {Bb S : ℕ}

theorem pkI_nil : pkI Bb S [] = I4.zero := by simp [pkI, pkc, I4.zero]

theorem pkI_cons (t : (ℕ × ℕ) × I4) (P : GP) :
    pkI Bb S (t :: P) = I4.add (I4.smul ((Bb ^ gpos S t.1 : ℕ) : ℤ) t.2) (pkI Bb S P) := by
  ext <;> simp [pkI, pkc, I4.add, I4.smul] <;> ring

theorem pkI_append (P Q : GP) : pkI Bb S (P ++ Q) = I4.add (pkI Bb S P) (pkI Bb S Q) := by
  ext <;> simp [pkI, pkc, I4.add]

theorem pkI_gscale (n : ℤ) (P : GP) : pkI Bb S (gscale n P) = I4.smul n (pkI Bb S P) := by
  induction P with
  | nil => ext <;> simp [gscale, pkI, pkc, I4.smul]
  | cons t P ih =>
    simp only [gscale, List.map_cons] at ih ⊢
    rw [pkI_cons, pkI_cons, ih]; ext <;> simp [I4.add, I4.smul] <;> ring

theorem pkI_gneg (P : GP) : pkI Bb S (gneg P) = I4.neg (pkI Bb S P) := by
  induction P with
  | nil => ext <;> simp [gneg, pkI, pkc, I4.neg]
  | cons t P ih =>
    simp only [gneg, List.map_cons] at ih ⊢
    rw [pkI_cons, pkI_cons, ih]; ext <;> simp [I4.add, I4.smul, I4.neg] <;> ring

theorem gpos_add (e f : ℕ × ℕ) : gpos S (e.1 + f.1, e.2 + f.2) = gpos S e + gpos S f := by
  simp [gpos]; ring

theorem pkI_row (A B : ℤ) (t : (ℕ × ℕ) × I4) (Q : GP) :
    pkI Bb S (Q.map fun u => ((t.1.1 + u.1.1, t.1.2 + u.1.2), I4.mul A B t.2 u.2)) =
      I4.mul A B (I4.smul ((Bb ^ gpos S t.1 : ℕ) : ℤ) t.2) (pkI Bb S Q) := by
  induction Q with
  | nil => ext <;> simp [pkI, pkc, I4.mul, I4.smul]
  | cons u Q ih =>
    rw [List.map_cons, pkI_cons, ih, pkI_cons, gpos_add]
    ext <;> simp [I4.add, I4.smul, I4.mul, pow_add, Nat.cast_mul] <;> ring

theorem pkI_gmul (A B : ℤ) (P Q : GP) :
    pkI Bb S (gmul A B P Q) = I4.mul A B (pkI Bb S P) (pkI Bb S Q) := by
  induction P with
  | nil => ext <;> simp [gmul, pkI, pkc, I4.mul]
  | cons t P ih =>
    simp only [gmul, List.flatMap_cons] at ih ⊢
    rw [pkI_append, pkI_row, ih, pkI_cons]
    ext <;> simp [I4.add, I4.smul, I4.mul] <;> ring

theorem gl1_append (P Q : GP) : gl1 (P ++ Q) = gl1 P + gl1 Q := by simp [gl1]

theorem gl1_gscale (n : ℤ) (P : GP) : gl1 (gscale n P) = n.natAbs * gl1 P := by
  induction P with
  | nil => simp [gl1, gscale]
  | cons t P ih =>
    simp only [gl1, gscale, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]; simp [I4.l1, I4.smul, Int.natAbs_mul]; ring

theorem gl1_gneg (P : GP) : gl1 (gneg P) = gl1 P := by
  induction P with
  | nil => simp [gl1, gneg]
  | cons t P ih =>
    simp only [gl1, gneg, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]; simp [I4.l1, I4.neg]

theorem gl1_row (A B : ℤ) (t : (ℕ × ℕ) × I4) (Q : GP) :
    gl1 (Q.map fun u => ((t.1.1 + u.1.1, t.1.2 + u.1.2), I4.mul A B t.2 u.2)) ≤
      I4.kappa A B * t.2.l1 * gl1 Q := by
  induction Q with
  | nil => simp [gl1]
  | cons u Q ih =>
    simp only [gl1, List.map_cons, List.sum_cons] at ih ⊢
    have := I4.l1_mul A B t.2 u.2
    nlinarith

theorem gl1_gmul (A B : ℤ) (P Q : GP) : gl1 (gmul A B P Q) ≤ I4.kappa A B * gl1 P * gl1 Q := by
  induction P with
  | nil => simp [gl1, gmul]
  | cons t P ih =>
    simp only [gmul, List.flatMap_cons] at ih ⊢
    rw [gl1_append]
    have h1 := gl1_row A B t Q
    have e : gl1 (t :: P) = t.2.l1 + gl1 P := by simp [gl1]
    rw [e]
    nlinarith

end Ghost

/-! ## Kroneckerlemmat -/

section Kron

/-- en heltalsserie med små siffror och packat värde 0 är noll -/
theorem digits_zero (Bb β : ℤ) (hB : 2 * β < Bb) :
    ∀ (M : ℕ) (g : ℕ → ℤ), (∀ n < M, |g n| ≤ β) →
      (∑ n ∈ Finset.range M, g n * Bb ^ n) = 0 → ∀ n < M, g n = 0
  | 0 => by intro g _ _ n hn; omega
  | M + 1 => by
    intro g hg hs
    rw [Finset.sum_range_succ'] at hs
    set X := ∑ n ∈ Finset.range M, g (n + 1) * Bb ^ n with hXdef
    have hX : (∑ n ∈ Finset.range M, g (n + 1) * Bb ^ (n + 1)) = Bb * X := by
      rw [hXdef, Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => ?_; ring
    rw [hX] at hs
    have hb0 := hg 0 (by omega)
    have hβ0 : 0 ≤ β := le_trans (abs_nonneg _) hb0
    have h0 : g 0 = -(Bb * X) := by simp at hs; linarith
    have hX0 : X = 0 := by
      by_contra hne
      have h1 : 1 ≤ |X| := Int.one_le_abs hne
      have h2 : |g 0| = Bb * |X| := by
        rw [h0, abs_neg, abs_mul, abs_of_pos (by linarith : (0 : ℤ) < Bb)]
      nlinarith
    have hg0 : g 0 = 0 := by rw [h0, hX0]; ring
    have rest := digits_zero Bb β hB M (fun n => g (n + 1)) (fun n hn => hg (n + 1) (by omega))
      (by rw [← hX0])
    intro n hn
    cases n with
    | zero => exact hg0
    | succ n => exact rest n (by omega)

theorem sum_fib {α R : Type} [AddCommMonoid R] (pos : α → ℕ) (h : α → R) (M : ℕ) :
    ∀ P : List α, (∀ t ∈ P, pos t < M) →
      (P.map h).sum = ∑ n ∈ Finset.range M, ((P.filter fun t => decide (pos t = n)).map h).sum
  | [], _ => by simp
  | t :: P, hP => by
    have ih := sum_fib pos h M P (fun u hu => hP u (by simp [hu]))
    have hc : ∀ n, ((List.filter (fun u => decide (pos u = n)) (t :: P)).map h).sum =
        (if pos t = n then h t else 0) + ((P.filter fun u => decide (pos u = n)).map h).sum := by
      intro n; by_cases e : pos t = n <;> simp [List.filter_cons, e]
    simp only [hc, Finset.sum_add_distrib, List.map_cons, List.sum_cons, ih]
    rw [Finset.sum_ite_eq]
    simp [hP t (by simp)]

theorem le_sum_of_mem' {α : Type} (f : α → ℕ) : ∀ (P : List α) (t : α), t ∈ P → f t ≤ (P.map f).sum
  | [], _, h => by simp at h
  | u :: P, t, h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · have := le_sum_of_mem' f P t h; simp; omega

theorem abs_fsum_le {α : Type} (p : α → Bool) (f w : α → ℤ) (hw : ∀ t, |f t| ≤ w t) :
    ∀ P : List α, |((P.filter p).map f).sum| ≤ (P.map w).sum
  | [] => by simp
  | t :: P => by
    have ih := abs_fsum_le p f w hw P
    have h0 : 0 ≤ w t := le_trans (abs_nonneg _) (hw t)
    by_cases h : p t
    · simp only [List.filter_cons, h, ite_true, List.map_cons, List.sum_cons]
      calc |f t + ((P.filter p).map f).sum| ≤ |f t| + |((P.filter p).map f).sum| := abs_add_le _ _
        _ ≤ w t + (P.map w).sum := add_le_add (hw t) ih
    · simp only [List.filter_cons, h, Bool.false_eq_true, ite_false, List.map_cons, List.sum_cons]
      linarith

variable {F : Type} [Field F]

/-- en komponent: packat värde 0 + små koefficienter + `a`-grad `< S` ⇒ summan är 0 -/
theorem comp_zero (Kb S : ℕ) (f : I4 → ℤ) (hf : ∀ x, |f x| ≤ (x.l1 : ℤ)) (P : GP) (β da : ℕ)
    (hpk : pkc (2 ^ Kb) S f P = 0) (hl : gl1 P ≤ β) (hd : ∀ t ∈ P, t.1.1 ≤ da) (hβ : 2 * β < 2 ^ Kb)
    (hS : da < S) (a b : F) :
    (P.map fun t => (f t.2 : F) * a ^ t.1.1 * b ^ t.1.2).sum = 0 := by
  set M := (P.map fun t => gpos S t.1).sum + 1
  have hM : ∀ t ∈ P, gpos S t.1 < M := by
    intro t ht; have := le_sum_of_mem' (fun t => gpos S t.1) P t ht; omega
  set g : ℕ → ℤ := fun n => ((P.filter fun t => decide (gpos S t.1 = n)).map fun t => f t.2).sum
  -- packat värde = Σ g n Bb^n
  have hpk2 : (∑ n ∈ Finset.range M, g n * ((2 ^ Kb : ℕ) : ℤ) ^ n) = 0 := by
    rw [← hpk, pkc, sum_fib (fun t => gpos S t.1) _ M P hM]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [g]
    have e : ((P.filter fun t => decide (gpos S t.1 = n)).map
        fun t => f t.2 * (((2 ^ Kb) ^ gpos S t.1 : ℕ) : ℤ)) =
        ((P.filter fun t => decide (gpos S t.1 = n)).map fun t => f t.2 * ((2 ^ Kb : ℕ) : ℤ) ^ n) := by
      refine List.map_congr_left fun t ht => ?_
      simp only [List.mem_filter, decide_eq_true_eq] at ht
      rw [ht.2]; push_cast; ring
    rw [e, List.sum_map_mul_right]
  have hg : ∀ n < M, |g n| ≤ (β : ℤ) := by
    intro n _
    simp only [g]
    calc |((P.filter fun t => decide (gpos S t.1 = n)).map fun t => f t.2).sum|
        ≤ ((P.map fun t => (t.2.l1 : ℤ))).sum := abs_fsum_le _ _ _ (fun t => hf t.2) P
      _ = (gl1 P : ℤ) := by simp [gl1, Nat.cast_list_sum, Function.comp_def]
      _ ≤ β := by exact_mod_cast hl
  have hB : 2 * (β : ℤ) < ((2 ^ Kb : ℕ) : ℤ) := by exact_mod_cast hβ
  have g0 := digits_zero _ _ hB M g hg hpk2
  rw [sum_fib (fun t => gpos S t.1) _ M P hM]
  refine Finset.sum_eq_zero fun n hn => ?_
  have hn' : n < M := Finset.mem_range.mp hn
  have e : ((P.filter fun t => decide (gpos S t.1 = n)).map
      fun t => (f t.2 : F) * a ^ t.1.1 * b ^ t.1.2) =
      ((P.filter fun t => decide (gpos S t.1 = n)).map
        fun t => (f t.2 : F) * (a ^ (n % S) * b ^ (n / S))) := by
    refine List.map_congr_left fun t ht => ?_
    simp only [List.mem_filter, decide_eq_true_eq] at ht
    have h1 : t.1.1 < S := lt_of_le_of_lt (hd t ht.1) hS
    have hS0 : 0 < S := by omega
    have e1 : n % S = t.1.1 := by
      rw [← ht.2, gpos, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]
    have e2 : n / S = t.1.2 := by
      rw [← ht.2, gpos, Nat.add_mul_div_left _ _ hS0, Nat.div_eq_of_lt h1, zero_add]
    rw [e1, e2]; ring
  rw [e, List.sum_map_mul_right]
  have : ((P.filter fun t => decide (gpos S t.1 = n)).map fun t => (f t.2 : F)).sum = (g n : F) := by
    simp only [g]; push_cast; simp [List.map_map, Function.comp_def]
  rw [this, g0 n hn']; simp

/-- tolkningen av spökpolynomet -/
def gval (a b r s : F) (P : GP) : F := (P.map fun t => I4.val r s t.2 * a ^ t.1.1 * b ^ t.1.2).sum

theorem gval_split (a b r s : F) (P : GP) : gval a b r s P =
    (P.map fun t => ((I4.a t.2 : ℤ) : F) * a ^ t.1.1 * b ^ t.1.2).sum +
    (P.map fun t => ((I4.b t.2 : ℤ) : F) * a ^ t.1.1 * b ^ t.1.2).sum * r +
    (P.map fun t => ((I4.c t.2 : ℤ) : F) * a ^ t.1.1 * b ^ t.1.2).sum * s +
    (P.map fun t => ((I4.d t.2 : ℤ) : F) * a ^ t.1.1 * b ^ t.1.2).sum * (r * s) := by
  induction P with
  | nil => simp [gval]
  | cons t P ih =>
    simp only [gval, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]; simp only [I4.val]; ring

/-- **Kroneckerlemmat.** -/
theorem kron_zero (Kb S : ℕ) (P : GP) (β da : ℕ) (hN : pkI (2 ^ Kb) S P = I4.zero)
    (hl : gl1 P ≤ β) (hd : ∀ t ∈ P, t.1.1 ≤ da) (hβ : 2 * β < 2 ^ Kb) (hS : da < S)
    (a b r s : F) : gval a b r s P = 0 := by
  have hN' := hN
  simp only [pkI, I4.zero, I4.mk.injEq] at hN'
  obtain ⟨ha, hb, hc, hd'⟩ := hN'
  have bnd : ∀ x : I4, |x.a| ≤ (x.l1 : ℤ) ∧ |x.b| ≤ (x.l1 : ℤ) ∧ |x.c| ≤ (x.l1 : ℤ) ∧
      |x.d| ≤ (x.l1 : ℤ) := by
    intro x; simp only [I4.l1, Nat.cast_add, Int.natCast_natAbs]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      linarith [abs_nonneg x.a, abs_nonneg x.b, abs_nonneg x.c, abs_nonneg x.d]
  rw [gval_split, comp_zero Kb S I4.a (fun x => (bnd x).1) P β da ha hl hd hβ hS,
    comp_zero Kb S I4.b (fun x => (bnd x).2.1) P β da hb hl hd hβ hS,
    comp_zero Kb S I4.c (fun x => (bnd x).2.2.1) P β da hc hl hd hβ hS,
    comp_zero Kb S I4.d (fun x => (bnd x).2.2.2) P β da hd' hl hd hβ hS]
  ring

theorem gval_append (a b r s : F) (P Q : GP) : gval a b r s (P ++ Q) = gval a b r s P + gval a b r s Q := by
  simp [gval]

theorem gval_gscale (a b r s : F) (n : ℤ) (P : GP) : gval a b r s (gscale n P) = n * gval a b r s P := by
  induction P with
  | nil => simp [gval, gscale]
  | cons t P ih =>
    simp only [gval, gscale, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]; simp only [I4.val, I4.smul]; push_cast; ring

theorem gval_gneg (a b r s : F) (P : GP) : gval a b r s (gneg P) = - gval a b r s P := by
  induction P with
  | nil => simp [gval, gneg]
  | cons t P ih =>
    simp only [gval, gneg, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]; simp only [I4.val, I4.neg]; push_cast; ring

theorem gval_row (A B : ℤ) (a b r s : F) (hr : r ^ 2 = A) (hs : s ^ 2 = B)
    (t : (ℕ × ℕ) × I4) (Q : GP) :
    gval a b r s (Q.map fun u => ((t.1.1 + u.1.1, t.1.2 + u.1.2), I4.mul A B t.2 u.2)) =
      I4.val r s t.2 * a ^ t.1.1 * b ^ t.1.2 * gval a b r s Q := by
  induction Q with
  | nil => simp [gval]
  | cons u Q ihQ =>
    simp only [gval, List.map_cons, List.sum_cons] at ihQ ⊢
    rw [ihQ, I4.val_mul A B r s hr hs]; ring

theorem gval_gmul (A B : ℤ) (a b r s : F) (hr : r ^ 2 = A) (hs : s ^ 2 = B) (P Q : GP) :
    gval a b r s (gmul A B P Q) = gval a b r s P * gval a b r s Q := by
  induction P with
  | nil => simp [gval, gmul]
  | cons t P ih =>
    simp only [gmul, List.flatMap_cons] at ih ⊢
    rw [gval_append, ih, gval_row A B a b r s hr hs]
    simp only [gval, List.map_cons, List.sum_cons]; ring

end Kron

/-! ## Modellen -/

/-- invarianten mellan packade tal och spökpolynom -/
def PInv (Kb S : ℕ) (N : I4) (den β da : ℕ) (P : GP) : Prop :=
  N = pkI (2 ^ Kb) S P ∧ gl1 P ≤ β ∧ (∀ t ∈ P, t.1.1 ≤ da) ∧ 0 < den

/-- `P / den`, med packade värden `N`, ℓ¹-gräns `β` och `a`-gradgräns `da` -/
structure PK (A B : ℤ) (Kb S : ℕ) where
  N : I4
  den : ℕ
  β : ℕ
  da : ℕ
  /-- spökpolynomet, fördröjt (räknas aldrig ut av kärnan eller av `#eval`) -/
  G : Unit → GP
  h : PInv Kb S N den β da (G ())

namespace PK
variable {A B : ℤ} {Kb S : ℕ}

/-- spökpolynomet -/
abbrev P (x : PK A B Kb S) : GP := x.G ()

def zero : PK A B Kb S := ⟨I4.zero, 1, 0, 0, fun _ => [], by simp [PInv, pkI_nil, gl1]⟩

/-- konstanten `c / den` -/
def const (c : I4) (den : ℕ) (hd : 0 < den) : PK A B Kb S :=
  ⟨c, den, c.l1, 0, fun _ => [((0, 0), c)],
    by refine ⟨by ext <;> simp [pkI, pkc, gpos], by simp [gl1], by simp, hd⟩⟩

def maxA (P : GP) : ℕ := P.foldr (fun t m => max t.1.1 m) 0

theorem le_maxA : ∀ (P : GP) (t : (ℕ × ℕ) × I4), t ∈ P → t.1.1 ≤ maxA P
  | [], _, h => by simp at h
  | u :: P, t, h => by
    simp only [List.mem_cons] at h
    simp only [maxA, List.foldr_cons]
    rcases h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (le_maxA P t h) (le_max_right _ _)

/-- ur en termlista (data): de packade talen, `β` och `da` räknas ut av kärnan; `den = max d 1` -/
def ofList' (P : GP) (d : ℕ) : PK A B Kb S :=
  ⟨pkI (2 ^ Kb) S P, max d 1, gl1 P, maxA P, fun _ => P, rfl, le_rfl, le_maxA P, by omega⟩

/-- ur en termlista (används för data): de packade talen räknas ut av kärnan -/
def ofList (P : GP) (den : ℕ) (hd : 0 < den) (da : ℕ) (hda : (P.all fun t => decide (t.1.1 ≤ da)) = true) :
    PK A B Kb S :=
  ⟨pkI (2 ^ Kb) S P, den, gl1 P, da, fun _ => P, rfl, le_rfl, by
    intro t ht; simp only [List.all_eq_true, decide_eq_true_eq] at hda; exact hda t ht, hd⟩

def add (x y : PK A B Kb S) : PK A B Kb S :=
  if hxy : x.den = y.den then
    ⟨I4.add x.N y.N, x.den, x.β + y.β, max x.da y.da, fun _ => x.P ++ y.P, by
      obtain ⟨h1, h2, h3, h4⟩ := x.h; obtain ⟨g1, g2, g3, _⟩ := y.h
      refine ⟨by rw [pkI_append, h1, g1], by rw [gl1_append]; exact Nat.add_le_add h2 g2, ?_, h4⟩
      intro t ht; rcases List.mem_append.mp ht with ht | ht
      · exact le_trans (h3 t ht) (le_max_left _ _)
      · exact le_trans (g3 t ht) (le_max_right _ _)⟩
  else
    ⟨I4.add (I4.smul y.den x.N) (I4.smul x.den y.N), x.den * y.den, y.den * x.β + x.den * y.β,
      max x.da y.da, fun _ => gscale y.den x.P ++ gscale x.den y.P, by
      obtain ⟨h1, h2, h3, h4⟩ := x.h; obtain ⟨g1, g2, g3, g4⟩ := y.h
      refine ⟨by rw [pkI_append, pkI_gscale, pkI_gscale, h1, g1], ?_, ?_, Nat.mul_pos h4 g4⟩
      · rw [gl1_append, gl1_gscale, gl1_gscale]; simp only [Int.natAbs_natCast]
        exact Nat.add_le_add (Nat.mul_le_mul_left _ h2) (Nat.mul_le_mul_left _ g2)
      · intro t ht; rcases List.mem_append.mp ht with ht | ht
        · simp only [gscale, List.mem_map] at ht; obtain ⟨u, hu, rfl⟩ := ht
          exact le_trans (h3 u hu) (le_max_left _ _)
        · simp only [gscale, List.mem_map] at ht; obtain ⟨u, hu, rfl⟩ := ht
          exact le_trans (g3 u hu) (le_max_right _ _)⟩

def mul (x y : PK A B Kb S) : PK A B Kb S :=
  ⟨I4.mul A B x.N y.N, x.den * y.den, I4.kappa A B * x.β * y.β, x.da + y.da, fun _ => gmul A B x.P y.P, by
    obtain ⟨h1, h2, h3, h4⟩ := x.h; obtain ⟨g1, g2, g3, g4⟩ := y.h
    refine ⟨by rw [pkI_gmul, h1, g1], ?_, ?_, Nat.mul_pos h4 g4⟩
    · exact le_trans (gl1_gmul A B x.P y.P)
        (Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) g2)
    · intro t ht
      simp only [gmul, List.mem_flatMap, List.mem_map] at ht
      obtain ⟨u, hu, v, hv, rfl⟩ := ht
      exact Nat.add_le_add (h3 u hu) (g3 v hv)⟩

def neg (x : PK A B Kb S) : PK A B Kb S :=
  ⟨I4.neg x.N, x.den, x.β, x.da, fun _ => gneg x.P, by
    obtain ⟨h1, h2, h3, h4⟩ := x.h
    refine ⟨by rw [pkI_gneg, h1], by rw [gl1_gneg]; exact h2, ?_, h4⟩
    intro t ht; simp only [gneg, List.mem_map] at ht; obtain ⟨u, hu, rfl⟩ := ht; exact h3 u hu⟩

def ofQ (q : ℚ) : PK A B Kb S := const ⟨q.num, 0, 0, 0⟩ q.den q.den_pos

/-- kärnans test: bara de packade talen och gränserna läses -/
def isZero (x : PK A B Kb S) : Bool :=
  I4.isZ x.N && decide (2 * x.β < 2 ^ Kb) && decide (x.da < S)

instance : Comp (PK A B Kb S) where
  zero := zero
  add := add
  mul := mul
  neg := neg
  ofQ := ofQ
  isZero := isZero

variable {F : Type} [Field F] [CharZero F]

/-- tolkningen `P(a, b) / den` -/
def val (a b r s : F) (x : PK A B Kb S) : F := gval a b r s x.P / x.den

theorem den_ne (x : PK A B Kb S) : (x.den : F) ≠ 0 := by
  have := x.h.2.2.2; exact_mod_cast this.ne'

theorem sound (a b r s : F) (hr : r ^ 2 = A) (hs : s ^ 2 = B) :
    Sound (val (A := A) (B := B) (Kb := Kb) (S := S) a b r s) where
  zero := by simp [val, Comp.zero, zero, gval, P]
  add x y := by
    simp only [val, Comp.add, add, P]
    have hx := den_ne (F := F) x; have hy := den_ne (F := F) y
    split_ifs with hxy
    · simp only [gval_append]; rw [hxy, add_div]
    · simp only [gval_append, gval_gscale]; push_cast
      field_simp
  mul x y := by
    simp only [val, Comp.mul, mul, P, gval_gmul A B a b r s hr hs]; push_cast
    rw [div_mul_div_comm]
  neg x := by simp only [val, Comp.neg, neg, P, gval_gneg]; ring
  ofQ q := by
    simp only [val, Comp.ofQ, ofQ, const, gval, I4.val, P]
    simp [Rat.cast_def]
  isZero x h := by
    simp only [Comp.isZero, isZero, I4.isZ, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, hβ⟩, hS⟩ := h
    obtain ⟨h1, h2, h3, _⟩ := x.h
    have hN : pkI (2 ^ Kb) S x.P = I4.zero := by
      rw [← h1]; ext <;> simp [I4.zero, ha, hb, hc, hd]
    simp only [val]
    rw [kron_zero Kb S x.P x.β x.da hN h2 h3 hβ hS a b r s, zero_div]

end PK

end X
end LeanResidy
