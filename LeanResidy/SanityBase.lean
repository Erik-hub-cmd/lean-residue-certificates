import LeanResidy.Points

/-!
# Generiska hjälpsatser för rimlighetskontrollerna (granskning 2026-11-24)

Skrivna i granskningen, inte av den som skrev resten av koden.
-/

namespace LeanResidy

variable {F : Type} [Field F]

/-- `xpar` är multiplikativ i exponenterna: `∏ (z−q)^{a·e + b·f} = (∏ (z−q)^e)^a · (∏ (z−q)^f)^b`. -/
theorem xpar_lin (qs : List F) (z : F) (hz : ∀ q ∈ qs, z ≠ q) (a b : ℤ) (e1 e2 : List ℤ)
    (hl : e1.length = e2.length) :
    xpar qs (List.zipWith (fun u w => a * u + b * w) e1 e2) z = xpar qs e1 z ^ a * xpar qs e2 z ^ b := by
  induction qs generalizing e1 e2 with
  | nil => simp [xpar]
  | cons q qs ih =>
    cases e1 with
    | nil =>
      cases e2 with
      | nil => simp [xpar]
      | cons _ _ => simp at hl
    | cons u e1 =>
      cases e2 with
      | nil => simp at hl
      | cons w e2 =>
        have hq : z - q ≠ 0 := sub_ne_zero.mpr (hz q (by simp))
        have ih' := ih (fun q' hq' => hz q' (by simp [hq'])) e1 e2 (by simpa using hl)
        simp only [xpar, List.zipWith_cons_cons, List.prod_cons] at ih' ⊢
        rw [ih', zpow_add₀ hq, mul_zpow, mul_zpow, mul_comm a u, mul_comm b w, zpow_mul, zpow_mul]
        ring

theorem xpar_ne_zero (qs : List F) (z : F) (hz : ∀ q ∈ qs, z ≠ q) (es : List ℤ) :
    xpar qs es z ≠ 0 := by
  rw [xpar_eq_pe]; exact pe_ne_zero qs z hz es

variable [CharZero F]

/-- Ett Laurentpolynom med rationella koefficienter i rationella punkter: värdet i `F` är
bilden av värdet i `ℚ`. -/
theorem leval_cast (L : LP) (a b : ℚ) : leval L (a : F) (b : F) = ((leval L a b : ℚ) : F) := by
  induction L with
  | nil => simp [leval]
  | cons t L ih =>
    simp only [leval, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]; push_cast; ring

end LeanResidy
