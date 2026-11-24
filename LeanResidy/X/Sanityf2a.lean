import LeanResidy.X.SanityBase
import LeanResidy.X.Casef2a

/-!
# Rimlighetssatser för [3².6²; 3.6.3.6] med lika vikter (granskning 2026-11-24, kväll)

Skrivna i granskningen, inte av den som skrev resten av koden. Kroppen är `ℚ(r, s, t)` med
`r² = −1`, `s² = 2`, `t² = 3`, alltså `ℚ(i, √2, √3)` (artikel 3, tabellen över spåren).
-/

set_option linter.unusedSectionVars false

namespace LeanResidy.X
namespace Cf2a
open LeanResidy.Comp

/-- `T` ligger i `SL₂(ℤ)`. -/
theorem T_det : data.t00 * data.t11 - data.t01 * data.t10 = 1 := by decide

theorem ex_ok : data.exOK = true := by decide +kernel
theorem shape_ok : data.shapeOK = true := by decide +kernel
theorem ok2 : data.okAt 2 = true := by decide +kernel

variable {F : Type} [Field F] [CharZero F] (r s t : F)

section
variable (hr : r ^ 2 = ((-1 : ℤ) : F)) (hs : s ^ 2 = ((2 : ℤ) : F)) (ht : t ^ 2 = ((3 : ℚ) : F))
include hr hs ht

omit hr hs ht in
/-- Alla sex kanter har ledningsförmåga 1. -/
theorem weights : data.E.map (fun e => vK r s t e.2.2.2.2) = [1, 1, 1, 1, 1, 1] := by
  simp [data, vK, Z8.val, Quad.val, Z4.val]

omit hr hs ht in
/-- `D` är (med tecknet −) Blochdeterminanten för [3².6²; 3.6.3.6] i artikel 3, avsnittet om gittren. -/
theorem D_eq (x1 x2 : F) (h1 : x1 ≠ 0) (h2 : x2 ≠ 0) :
    levalK (vK r s t) data.D x1 x2 =
      -(x1 ^ 2 * x2 ^ 2 + 10 * x1 ^ 2 * x2 + x1 ^ 2 + 6 * x1 * x2 ^ 2 - 36 * x1 * x2 + 6 * x1 + x2 ^ 2 +
        10 * x2 + 1) / (x1 * x2) := by
  simp [levalK, data, vK, Z8.val, Quad.val, Z4.val]
  field_simp
  ring

omit hr hs ht in
/-- `D(−1, −1) = 64 ≠ 0`. -/
theorem D_ne_zero : levalK (vK r s t) data.D (-1) (-1) ≠ 0 := by
  rw [D_eq r s t _ _ (by norm_num) (by norm_num)]
  norm_num

theorem green (x1 x2 : F) (h1 : x1 ≠ 0) (h2 : x2 ≠ 0) (hD : levalK (vK r s t) data.D x1 x2 ≠ 0) :
    (lapMatK (vK r s t) data.V data.E x1 x2)⁻¹ =
      (levalK (vK r s t) data.D x1 x2)⁻¹ • lmatK (vK r s t) data.V data.A x1 x2 :=
  green_gen data x1 x2 (adjugate r s t hr hs ht x1 x2 h1 h2) hD

omit hr hs ht in
theorem x_eq_vT (z : F) (hz : ∀ q ∈ qv (vK r s t) data, z ≠ q) :
    xpar (qv (vK r s t) data) data.ex1 z =
        xpar (qv (vK r s t) data) data.ev1 z ^ data.t00 * xpar (qv (vK r s t) data) data.ev2 z ^ data.t10 ∧
    xpar (qv (vK r s t) data) data.ex2 z =
        xpar (qv (vK r s t) data) data.ev1 z ^ data.t01 * xpar (qv (vK r s t) data) data.ev2 z ^ data.t11 :=
  x_eq_vT_gen data ex_ok z hz

theorem curve_v (z : F) (hz : ∀ q ∈ qv (vK r s t) data, z ≠ q) :
    levalK (vK r s t) data.DT (xpar (qv (vK r s t) data) data.ev1 z) (xpar (qv (vK r s t) data) data.ev2 z) = 0 :=
  curve_v_gen data ex_ok z hz (curve r s t hr hs ht z hz)

omit hr hs ht in
theorem eulInv2_ok : invOK (data.eulAt 2) (CInv.inv (data.eulAt 2)) = true := by decide +kernel

/-- Nämnaren `v₂∂_{v₂}D^T(v(z))` är ≠ 0 i `z = 2`, för alla åtta val av rötterna. -/
theorem eul_ne_zero_at_2 :
    levalK (vK r s t) (eulK data.DT) (xpar (qv (vK r s t) data) data.ev1 ((2 : ℚ) : F))
      (xpar (qv (vK r s t) data) data.ev2 ((2 : ℚ) : F)) ≠ 0 :=
  eul_ne_zero_gen data (sound r s t hr hs ht) 2 _ ok2 eulInv2_ok

theorem integrand (k l : Fin data.V) (z : F) (hz : ∀ q ∈ qv (vK r s t) data, z ≠ q)
    (hE : levalK (vK r s t) (eulK data.DT) (xpar (qv (vK r s t) data) data.ev1 z)
      (xpar (qv (vK r s t) data) data.ev2 z) ≠ 0) :
    levalK (vK r s t) (data.A k l) (xpar (qv (vK r s t) data) data.ex1 z)
        (xpar (qv (vK r s t) data) data.ex2 z) * dlogv (qv (vK r s t) data) data.ev1 z /
        levalK (vK r s t) (eulK data.DT) (xpar (qv (vK r s t) data) data.ev1 z)
          (xpar (qv (vK r s t) data) data.ev2 z) =
      pfval (qv (vK r s t) data) ((data.pfin k l).map fun t' => (t'.1, t'.2.1, vK r s t t'.2.2)) [] z :=
  integrand_gen data shape_ok k l z (partial_fractions r s t hr hs ht k l z hz) hE

end

theorem pinf_nil (k l : ℕ) : data.pinf k l = [] := pinf_nil_gen data shape_ok k l

theorem pfin_zero_simple (k l : ℕ) : ∀ t ∈ data.pfin k l, t.1 = data.iz → t.2.1 = 1 :=
  pfin_zero_simple_gen data shape_ok k l

end Cf2a
end LeanResidy.X
