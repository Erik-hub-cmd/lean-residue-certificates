import LeanResidy.X.Dataf2awK
import LeanResidy.X.Dataf2bwK

/-!
# Rimlighet: nämnarhypotesen `hD` gäller på hela det fysikaliska området

Skriven i en separat kontroll (2026-11-25), inte i samma session som resten av koden.

Nämnarlistorna `Dl` innehåller, utöver de äkta faktorerna (punkteringar som sammanfaller, vikter som
blir 0 eller ∞), faktorer av formen `k + e·m` med ett heltal `|k| ≥ 2`, `e ∈ {±1, ±r}` och ett monom
`m ∈ {ab, a, b}`. De kommer från kontrollpunkterna `z = 2, 3, …` (`z − q` för en punktering `q`) och
har inget med problemet att göra. Här visas att de alla är ≠ 0 när monomet har belopp 1, och därmed:

* f2a (`a = P₁`, `b = P₂`): `hD` gäller för alla `a, b` på enhetscirkeln med `a ≠ ±b`, `a² ≠ −1`,
  `b² ≠ −1`, `ab ≠ −1`. Det fysikaliska området (`ab = e^{iφ₁}`, `a/b = e^{iφ₂}`, `φ₁, φ₂ ∈ (0, π)`,
  `φ₁ + φ₂ < π`, smal_g2a/BEVIS.md §0) ligger där.
* f2b (`a = u = e^{iθ}`, `b = r = w₁/w₀`): `hD` gäller för alla `u` på enhetscirkeln med `u ≠ ±1`,
  `u² ≠ −1` och alla `b ≠ 0, −1`. Det fysikaliska området (`θ ∈ (0, π/2)`, `b > 0`, artikel 3,
  bevis av Sats `thm:f2bt`) ligger där.
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace LeanResidy.X
namespace KronUnit
open Complex

deriving instance DecidableEq for I4

/-- `k + e · aⁱ bʲ` med `|k| ≥ 2`, `e ∈ {±1, ±r}` och `(i, j) ∈ mons` -/
def isArt (mons : List (ℕ × ℕ)) : GP → Bool
  | [((0, 0), c), ((i, j), e)] =>
      c.b == 0 && c.c == 0 && c.d == 0 && decide (2 ≤ c.a.natAbs) && e.c == 0 && e.d == 0 &&
        ((e.a.natAbs == 1 && e.b == 0) || (e.a == 0 && e.b.natAbs == 1)) && decide ((i, j) ∈ mons)
  | _ => false

theorem normSq_r (r : ℂ) (hr : r ^ 2 = ((-1 : ℤ) : ℂ)) : normSq r = 1 := by
  have h : normSq r ^ 2 = 1 := by rw [← map_pow, hr]; simp
  have h0 := normSq_nonneg r
  nlinarith [sq_nonneg (normSq r - 1), sq_nonneg (normSq r + 1)]

theorem normSq_unit_int (n : ℤ) (h : n.natAbs = 1) : normSq (n : ℂ) = 1 := by
  rcases Int.natAbs_eq_iff.mp h with h | h <;> rw [h] <;> simp

theorem art_ne (mons : List (ℕ × ℕ)) (a b r s : ℂ) (hr : r ^ 2 = ((-1 : ℤ) : ℂ))
    (hm : ∀ p ∈ mons, normSq (a ^ p.1 * b ^ p.2) = 1) (P : GP) (h : isArt mons P = true) :
    gval a b r s P ≠ 0 := by
  match P, h with
  | [((0, 0), c), ((i, j), e)], h =>
    simp only [isArt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨hcb, hcc⟩, hcd⟩, hk⟩, hec⟩, hed⟩, he⟩, hij⟩ := h
    have hmon : normSq (a ^ i * b ^ j) = 1 := hm (i, j) hij
    have hev : normSq (I4.val r s e) = 1 := by
      simp only [I4.val, hec, hed, Int.cast_zero, zero_mul, add_zero]
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2]; simp only [Int.cast_zero, zero_mul, add_zero]; exact normSq_unit_int _ h1
      · rw [h1]; simp only [Int.cast_zero, zero_add, map_mul, normSq_r r hr, mul_one]
        exact normSq_unit_int _ h2
    intro h0
    simp only [gval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, pow_zero,
      mul_one] at h0
    have hc : I4.val r s c = (c.a : ℂ) := by simp [I4.val, hcb, hcc, hcd]
    rw [hc] at h0
    have e1 : (c.a : ℂ) = -(I4.val r s e * (a ^ i * b ^ j)) := by linear_combination h0
    have e2 : normSq (c.a : ℂ) = 1 := by rw [e1, Complex.normSq_neg, map_mul, hev, hmon, one_mul]
    rw [normSq_intCast] at e2
    have e3 : ((c.a * c.a : ℤ) : ℝ) = 1 := by push_cast; exact e2
    have e4 : c.a * c.a = 1 := by exact_mod_cast e3
    have hk2 : (2 : ℤ) ≤ (c.a.natAbs : ℤ) := by exact_mod_cast hk
    rcases Int.natAbs_eq c.a with h | h <;> rw [h] at e4 <;> nlinarith

/-! ## f2a -/

/-- de äkta faktorerna i `Cf2awK.Dl` -/
def gen2a : List GP :=
  [[((0, 1), ⟨1, 0, 0, 0⟩), ((1, 0), ⟨-1, 0, 0, 0⟩)],
   [((0, 0), ⟨0, -1, 0, 0⟩), ((1, 0), ⟨1, 0, 0, 0⟩)],
   [((0, 0), ⟨0, 1, 0, 0⟩), ((1, 0), ⟨1, 0, 0, 0⟩)],
   [((0, 0), ⟨0, -1, 0, 0⟩), ((0, 1), ⟨1, 0, 0, 0⟩)],
   [((0, 0), ⟨0, 1, 0, 0⟩), ((0, 1), ⟨1, 0, 0, 0⟩)],
   [((1, 0), ⟨1, 0, 0, 0⟩)],
   [((0, 1), ⟨1, 0, 0, 0⟩)],
   [((0, 1), ⟨1, 0, 0, 0⟩), ((1, 0), ⟨1, 0, 0, 0⟩)],
   [((0, 0), ⟨1, 0, 0, 0⟩), ((1, 1), ⟨1, 0, 0, 0⟩)]]

/-- varje faktor i `Dl` är antingen en kontrollpunktsfaktor eller en av de nio äkta -/
theorem dl2a_shape :
    Cf2awK.Dl.all (fun d => isArt [(1, 1), (1, 0), (0, 1)] d.P || decide (d.P ∈ gen2a)) = true := by
  decide +kernel

/-- **`hD` för f2a på enhetscirkeln.** -/
theorem f2a_hD_unit (a b r s : ℂ) (hr : r ^ 2 = ((-1 : ℤ) : ℂ)) (ha : normSq a = 1) (hb : normSq b = 1)
    (h1 : a ≠ b) (h2 : a ≠ -b) (h3 : a ^ 2 ≠ -1) (h4 : b ^ 2 ≠ -1) (h5 : a * b ≠ -1) :
    ∀ d ∈ Cf2awK.Dl, PK.val a b r s d ≠ 0 := by
  have hr' : r ^ 2 = -1 := by rw [hr]; push_cast; ring
  have hm : ∀ p ∈ [((1 : ℕ), (1 : ℕ)), (1, 0), (0, 1)], normSq (a ^ p.1 * b ^ p.2) = 1 := by
    intro p hp; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [map_mul, ha, hb]
  intro d hd
  have hc := List.all_eq_true.mp dl2a_shape d hd
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
  show gval a b r s d.P / (d.den : ℂ) ≠ 0
  refine div_ne_zero ?_ (PK.den_ne d)
  rcases hc with hc | hc
  · exact art_ne _ a b r s hr hm d.P hc
  · simp only [gen2a, List.mem_cons, List.mem_nil_iff, or_false] at hc
    intro h0
    rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc <;> rw [hc] at h0 <;>
      simp only [gval, I4.val, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h0 <;>
      push_cast at h0
    · exact h1 (by linear_combination -h0)
    · exact h3 (by linear_combination (a + r) * h0 + hr')
    · exact h3 (by linear_combination (a - r) * h0 + hr')
    · exact h4 (by linear_combination (b + r) * h0 + hr')
    · exact h4 (by linear_combination (b - r) * h0 + hr')
    · have : a = 0 := by linear_combination h0
      rw [this] at ha; simp at ha
    · have : b = 0 := by linear_combination h0
      rw [this] at hb; simp at hb
    · exact h2 (by linear_combination h0)
    · exact h5 (by linear_combination h0)

/-! ## f2b -/

/-- de äkta faktorerna i `Cf2bwK.Dl` -/
def gen2b : List GP :=
  [[((1, 0), ⟨1, 0, 0, 0⟩)],
   [((0, 0), ⟨-1, 0, 0, 0⟩), ((1, 0), ⟨1, 0, 0, 0⟩)],
   [((0, 0), ⟨1, 0, 0, 0⟩), ((1, 0), ⟨1, 0, 0, 0⟩)],
   [((0, 0), ⟨1, 0, 0, 0⟩), ((2, 0), ⟨1, 0, 0, 0⟩)],
   [((0, 1), ⟨1, 0, 0, 0⟩)],
   [((0, 0), ⟨1, 0, 0, 0⟩), ((0, 1), ⟨1, 0, 0, 0⟩)]]

theorem dl2b_shape :
    Cf2bwK.Dl.all (fun d => isArt [(1, 0)] d.P || decide (d.P ∈ gen2b)) = true := by
  decide +kernel

/-- **`hD` för f2b för alla `u` på enhetscirkeln (utom ±1, ±i) och alla `b ≠ 0, −1`.** -/
theorem f2b_hD_unit (a b r s : ℂ) (hr : r ^ 2 = ((-1 : ℤ) : ℂ)) (ha : normSq a = 1)
    (h1 : a ≠ 1) (h2 : a ≠ -1) (h3 : a ^ 2 ≠ -1) (h4 : b ≠ 0) (h5 : b ≠ -1) :
    ∀ d ∈ Cf2bwK.Dl, PK.val a b r s d ≠ 0 := by
  have hm : ∀ p ∈ [((1 : ℕ), (0 : ℕ))], normSq (a ^ p.1 * b ^ p.2) = 1 := by
    intro p hp; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    subst hp; simp [ha]
  intro d hd
  have hc := List.all_eq_true.mp dl2b_shape d hd
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
  show gval a b r s d.P / (d.den : ℂ) ≠ 0
  refine div_ne_zero ?_ (PK.den_ne d)
  rcases hc with hc | hc
  · exact art_ne _ a b r s hr hm d.P hc
  · simp only [gen2b, List.mem_cons, List.mem_nil_iff, or_false] at hc
    intro h0
    rcases hc with hc | hc | hc | hc | hc | hc <;> rw [hc] at h0 <;>
      simp only [gval, I4.val, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h0 <;>
      push_cast at h0
    · have : a = 0 := by linear_combination h0
      rw [this] at ha; simp at ha
    · exact h1 (by linear_combination h0)
    · exact h2 (by linear_combination h0)
    · exact h3 (by linear_combination h0)
    · exact h4 (by linear_combination h0)
    · exact h5 (by linear_combination h0)

end KronUnit
end LeanResidy.X
