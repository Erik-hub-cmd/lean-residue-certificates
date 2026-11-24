import LeanResidy.X.SanityBase
import LeanResidy.X.Case3122t

/-!
# Rimlighetssatser för 3.12² med vikt t (granskning 2026-11-24, kväll)

Skrivna i granskningen, inte av den som skrev resten av koden. Parametern heter `u` i koden och `t` i
artikel 3 (Sats `thm:3122t`): ledningsförmåga 1 på triangelkanterna och `u` på 12–12-kanterna.
-/

set_option linter.unusedSectionVars false

namespace LeanResidy.X
namespace C3122t
open LeanResidy.Comp

/-- `T` ligger i `SL₂(ℤ)`. -/
theorem T_det : data.t00 * data.t11 - data.t01 * data.t10 = 1 := by decide

theorem ex_ok : data.exOK = true := by decide +kernel
theorem shape_ok : data.shapeOK = true := by decide +kernel
theorem ok2 : data.okAt 2 = true := by decide +kernel

variable {F : Type} [Field F] [CharZero F] (r s u : F)

section
variable (hr : r ^ 2 = ((-3 : ℤ) : F)) (hs : s ^ 2 = ((-1 : ℤ) : F))
  (hu : ∀ p ∈ tpts, u ≠ Z4.val r s p)
include hr hs hu

/-- Kantvikterna: 1 på de sex triangelkanterna, `u` på de tre 12–12-kanterna (0–3, 1–2, 4–5). -/
theorem weights : data.E.map (fun e => (e.1, e.2.1, vK r s u e.2.2.2.2)) =
    [(0, 4, 1), (0, 3, u), (0, 2, 1), (1, 2, u), (1, 5, 1), (1, 3, 1), (2, 4, 1), (4, 5, u), (3, 5, 1)] := by
  simp [data, vK, Fr.val, P.val, Fr.dval, tpts, Z4.val]

/-- `D = −3u²(2u + 3)·P_△` med `P_△ = x₁ + x₁⁻¹ + x₂ + x₂⁻¹ + x₁x₂⁻¹ + x₁⁻¹x₂ − 6`, som i artikel 3,
Proposition `prop:weights`(a) (med `w₀ = 1`, `w₁ = u`). -/
theorem D_eq (x1 x2 : F) (h1 : x1 ≠ 0) (h2 : x2 ≠ 0) :
    levalK (vK r s u) data.D x1 x2 =
      -3 * u ^ 2 * (2 * u + 3) * (x1 + x1⁻¹ + x2 + x2⁻¹ + x1 * x2⁻¹ + x1⁻¹ * x2 - 6) := by
  have h0 : u ≠ 0 := by simpa [tpts, Z4.val] using hu ⟨0, 0, 0, 0⟩ (by simp [tpts])
  simp [levalK, data, vK, Fr.val, P.val, Fr.dval, tpts, Z4.val]
  field_simp
  ring

/-- `D` är inte nollpolynomet för något tillåtet `u`: `D(−1, −1) = 24u²(2u + 3) ≠ 0`. -/
theorem D_ne_zero : levalK (vK r s u) data.D (-1) (-1) ≠ 0 := by
  have h0 : u ≠ 0 := by simpa [tpts, Z4.val] using hu ⟨0, 0, 0, 0⟩ (by simp [tpts])
  have h3 : u ≠ -3/2 := by simpa [tpts, Z4.val] using hu ⟨-3/2, 0, 0, 0⟩ (by simp [tpts])
  rw [D_eq r s u hr hs hu _ _ (by norm_num) (by norm_num)]
  have : (2 * u + 3) ≠ 0 := by
    intro h; apply h3; linear_combination h / 2
  have : (-3 : F) * u ^ 2 * (2 * u + 3) * ((-1) + (-1)⁻¹ + (-1) + (-1)⁻¹ + (-1) * (-1)⁻¹ + (-1)⁻¹ * (-1) - 6)
      = 24 * u ^ 2 * (2 * u + 3) := by norm_num; ring
  rw [this]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 h0)) ‹_›

theorem green (x1 x2 : F) (h1 : x1 ≠ 0) (h2 : x2 ≠ 0) (hD : levalK (vK r s u) data.D x1 x2 ≠ 0) :
    (lapMatK (vK r s u) data.V data.E x1 x2)⁻¹ =
      (levalK (vK r s u) data.D x1 x2)⁻¹ • lmatK (vK r s u) data.V data.A x1 x2 :=
  green_gen data x1 x2 (adjugate r s u hr hs hu x1 x2 h1 h2) hD

omit hr hs hu in
theorem x_eq_vT (z : F) (hz : ∀ q ∈ qv (vK r s u) data, z ≠ q) :
    xpar (qv (vK r s u) data) data.ex1 z =
        xpar (qv (vK r s u) data) data.ev1 z ^ data.t00 * xpar (qv (vK r s u) data) data.ev2 z ^ data.t10 ∧
    xpar (qv (vK r s u) data) data.ex2 z =
        xpar (qv (vK r s u) data) data.ev1 z ^ data.t01 * xpar (qv (vK r s u) data) data.ev2 z ^ data.t11 :=
  x_eq_vT_gen data ex_ok z hz

theorem curve_v (z : F) (hz : ∀ q ∈ qv (vK r s u) data, z ≠ q) :
    levalK (vK r s u) data.DT (xpar (qv (vK r s u) data) data.ev1 z) (xpar (qv (vK r s u) data) data.ev2 z) = 0 :=
  curve_v_gen data ex_ok z hz (curve r s u hr hs hu z hz)

/-- In `z = 2` är nämnaren `(360 − 136r)/7 · u²(u + 3/2)`; inversen anges här och kärnan kontrollerar
produkten. -/
def eulInv2 : K := ⟨[CInv.inv (⟨360/7, -136/7, 0, 0⟩ : Z4 (-3) (-1))], [2, 1]⟩

omit hr hs hu in
theorem eulInv2_ok : invOK (data.eulAt 2) eulInv2 = true := by decide +kernel

/-- Nämnaren `v₂∂_{v₂}D^T(v(z))` är inte identiskt noll längs parametriseringen, för **varje** tillåtet
`u` (≠ 0 i `z = 2`). -/
theorem eul_ne_zero_at_2 :
    levalK (vK r s u) (eulK data.DT) (xpar (qv (vK r s u) data) data.ev1 ((2 : ℚ) : F))
      (xpar (qv (vK r s u) data) data.ev2 ((2 : ℚ) : F)) ≠ 0 :=
  eul_ne_zero_gen data (sound r s u hr hs hu) 2 eulInv2 ok2 eulInv2_ok

theorem integrand (k l : Fin data.V) (z : F) (hz : ∀ q ∈ qv (vK r s u) data, z ≠ q)
    (hE : levalK (vK r s u) (eulK data.DT) (xpar (qv (vK r s u) data) data.ev1 z)
      (xpar (qv (vK r s u) data) data.ev2 z) ≠ 0) :
    levalK (vK r s u) (data.A k l) (xpar (qv (vK r s u) data) data.ex1 z)
        (xpar (qv (vK r s u) data) data.ex2 z) * dlogv (qv (vK r s u) data) data.ev1 z /
        levalK (vK r s u) (eulK data.DT) (xpar (qv (vK r s u) data) data.ev1 z)
          (xpar (qv (vK r s u) data) data.ev2 z) =
      pfval (qv (vK r s u) data) ((data.pfin k l).map fun t' => (t'.1, t'.2.1, vK r s u t'.2.2)) [] z :=
  integrand_gen data shape_ok k l z (partial_fractions r s u hr hs hu k l z hz) hE

end

theorem pinf_nil (k l : ℕ) : data.pinf k l = [] := pinf_nil_gen data shape_ok k l

theorem pfin_zero_simple (k l : ℕ) : ∀ t ∈ data.pfin k l, t.1 = data.iz → t.2.1 = 1 :=
  pfin_zero_simple_gen data shape_ok k l

end C3122t
end LeanResidy.X
