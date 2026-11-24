import LeanResidy.X.SanityBase
import LeanResidy.X.Case488u

/-!
# Rimlighetssatser för 4.8² med vikt t (granskning 2026-11-24, kväll)

Skrivna i granskningen, inte av den som skrev resten av koden. Artikel 3, Sats `thm:488t`: ledningsförmåga
`1 − c` på kvadratkanterna och `2c` på oktagon–oktagon-kanterna, `c = (u + u⁻¹)/2 = cos θ_t`, alltså
proportionellt mot `(1, t)` med `t = 2c/(1 − c)`. Parametern `u = e^{iθ_t}` ligger på enhetscirkeln.
-/

set_option linter.unusedSectionVars false

namespace LeanResidy.X
namespace C488u
open LeanResidy.Comp

/-- `T` ligger i `SL₂(ℤ)`. -/
theorem T_det : data.t00 * data.t11 - data.t01 * data.t10 = 1 := by decide

theorem ex_ok : data.exOK = true := by decide +kernel
theorem shape_ok : data.shapeOK = true := by decide +kernel
theorem ok2 : data.okAt 2 = true := by decide +kernel

variable {F : Type} [Field F] [CharZero F] (r s u : F)

section
variable (hr : r ^ 2 = ((-1 : ℤ) : F)) (hs : s ^ 2 = ((-2 : ℤ) : F))
  (hu : ∀ p ∈ tpts, u ≠ Z4.val r s p)
include hr hs hu

theorem u_ne_zero : u ≠ 0 := by simpa [tpts, Z4.val] using hu ⟨0, 0, 0, 0⟩ (by simp [tpts])

/-- Kantvikterna: `1 − c` på kvadratens fyra kanter (0–1, 1–2, 2–3, 3–0), `2c` på oktagon–oktagon-kanterna
0–2 (cell (1, 0)) och 1–3 (cell (0, 1)), `c = (u + u⁻¹)/2`. -/
theorem weights : data.E.map (fun e => (e.1, e.2.1, e.2.2.1, e.2.2.2.1, vK r s u e.2.2.2.2)) =
    [(0, 1, 0, 0, 1 - (u + u⁻¹) / 2), (1, 2, 0, 0, 1 - (u + u⁻¹) / 2), (2, 3, 0, 0, 1 - (u + u⁻¹) / 2),
      (3, 0, 0, 0, 1 - (u + u⁻¹) / 2), (0, 2, 1, 0, 2 * ((u + u⁻¹) / 2)), (1, 3, 0, 1, 2 * ((u + u⁻¹) / 2))] := by
  have h0 := u_ne_zero r s u hr hs hu
  simp [data, vK, Fr.val, P.val, Fr.dval, tpts, Z4.val]
  refine ⟨?_, ?_⟩ <;> (field_simp; ring)

/-- `D` är Blochdeterminanten `P_{W,D} = c₀ − W X₁ − W X₂ − D' X₁X₂` (`X_k = x_k + x_k⁻¹`,
`c₀ = 4W + 4D'`) med `W = 2a²b(2a + b)`, `D' = a²b²`, `a = 1 − c`, `b = 2c`, som i artikel 3,
Proposition `prop:weights`(b). -/
theorem D_eq (x1 x2 : F) (h1 : x1 ≠ 0) (h2 : x2 ≠ 0) :
    let c := (u + u⁻¹) / 2
    let a := 1 - c
    let b := 2 * c
    let W := 2 * a ^ 2 * b * (2 * a + b)
    let Dd := a ^ 2 * b ^ 2
    levalK (vK r s u) data.D x1 x2 =
      (2 * W + 2 * W + 4 * Dd) - W * (x1 + x1⁻¹) - W * (x2 + x2⁻¹) - Dd * (x1 + x1⁻¹) * (x2 + x2⁻¹) := by
  have h0 := u_ne_zero r s u hr hs hu
  simp [levalK, data, vK, Fr.val, P.val, Fr.dval, tpts, Z4.val]
  field_simp
  ring

/-- `D` är inte nollpolynomet för något tillåtet `u`: `D(−1, −1) = 8W = 32(1 − c)²·2c ≠ 0`. -/
theorem D_ne_zero : levalK (vK r s u) data.D (-1) (-1) ≠ 0 := by
  have h0 := u_ne_zero r s u hr hs hu
  have h1 : u ≠ 1 := by simpa [tpts, Z4.val] using hu ⟨1, 0, 0, 0⟩ (by simp [tpts])
  have h3 : u ≠ r := by simpa [tpts, Z4.val] using hu ⟨0, 1, 0, 0⟩ (by simp [tpts])
  have h4 : u ≠ -r := by simpa [tpts, Z4.val] using hu ⟨0, -1, 0, 0⟩ (by simp [tpts])
  rw [D_eq r s u hr hs hu _ _ (by norm_num) (by norm_num)]
  have e : u ^ 2 + 1 = (u - r) * (u + r) := by linear_combination hr
  have hq : u ^ 2 + 1 ≠ 0 := by
    rw [e]; exact mul_ne_zero (sub_ne_zero.mpr h3) (by intro h; apply h4; linear_combination h)
  have h1' : u - 1 ≠ 0 := sub_ne_zero.mpr h1
  intro h
  have h8 : 8 * (u - 1) ^ 4 * (u ^ 2 + 1) / u ^ 3 = 0 := by
    rw [← h]; field_simp; ring
  rw [div_eq_zero_iff] at h8
  rcases h8 with h8 | h8
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 4 h1')) hq h8
  · exact pow_ne_zero 3 h0 h8

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

/-- I `z = 2` är nämnaren `(4/5 + 4r/3)(u − 1)⁴(u + 1)³(u² + 1)(u² + 4)·Q(u) / (nämnare)` med
`Q(u) = (u − 4r)(u² + (−32/17 + 8r/17)u − 4r)`. `eulG2` tar bort allt utom `Q`, `eulQ` är `Q`. -/
def eulG2 : K := ⟨P.scale (CInv.inv (⟨4/5, 4/3, 0, 0⟩ : Z4 (-1) (-2))) (Fr.fac tpts [4, 0, 0, 0, 0, 1, 1, 2, 2]),
  [0, 4, 3, 1, 1, 0, 0, 1, 1]⟩
def eulQ : K := ⟨[⟨-16, 0, 0, 0⟩, ⟨32/17, 60/17, 0, 0⟩, ⟨-32/17, -60/17, 0, 0⟩, ⟨1, 0, 0, 0⟩], []⟩

omit hr hs hu in
theorem eulQ_ok : Comp.isZero (Comp.add (Comp.mul (data.eulAt 2) eulG2) (Comp.neg eulQ)) = true := by
  decide +kernel

/-- Nämnaren `v₂∂_{v₂}D^T(v(z))` är ≠ 0 i `z = 2` för varje tillåtet `u` utom nollställena till
`Q(u) = (u − 4r)(u² + (−32/17 + 8r/17)u − 4r)`; de har belopp 4, ca 1,53 och 2,62, så för `u` på
enhetscirkeln är villkoret uppfyllt (`hQ_unit` nedan). -/
theorem eul_ne_zero_at_2 (hQ : (u - 4 * r) * (u ^ 2 + (-32/17 + 8/17 * r) * u - 4 * r) ≠ 0) :
    levalK (vK r s u) (eulK data.DT) (xpar (qv (vK r s u) data) data.ev1 ((2 : ℚ) : F))
      (xpar (qv (vK r s u) data) data.ev2 ((2 : ℚ) : F)) ≠ 0 := by
  have S := sound r s u hr hs hu
  rw [← val_eulAt data S 2 ok2]
  have h := S.isZero _ eulQ_ok
  rw [S.add, S.mul, S.neg] at h
  have hv : vK r s u eulQ = (u - 4 * r) * (u ^ 2 + (-32/17 + 8/17 * r) * u - 4 * r) := by
    simp [eulQ, vK, Fr.val, P.val, Fr.dval, Z4.val]
    linear_combination (32/17 * u - 16) * hr
  intro h0
  rw [h0, zero_mul, zero_add, hv] at h
  exact hQ (by linear_combination -h)

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

/-! ### Enhetscirkeln: hypoteserna gäller för alla `u = e^{iθ}` utom `±1, ±i` -/

theorem tpts_shape : tpts.all (fun p => p.c == 0 && p.d == 0 && p.a * p.b == 0 &&
    (p.a ^ 2 + p.b ^ 2 == 0 || p.a ^ 2 + p.b ^ 2 == 1 || decide (4 ≤ p.a ^ 2 + p.b ^ 2))) = true := by
  decide +kernel

open Complex in
/-- Varje `u ∈ ℂ` med `|u| = 1` (`normSq u = 1`), `u ≠ ±1, ±i`, uppfyller hypotesen `hu` (med `r = i` och
valfritt `s`). -/
theorem hu_unit (s : ℂ) (u : ℂ) (h1 : Complex.normSq u = 1) (hp1 : u ≠ 1) (hm1 : u ≠ -1) (hpi : u ≠ I)
    (hmi : u ≠ -I) : ∀ p ∈ tpts, u ≠ Z4.val I s p := by
  intro p hp heq
  have h := tpts_shape
  simp only [List.all_eq_true] at h
  have hp' := h p hp
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hp'
  obtain ⟨⟨⟨hc, hd⟩, hab⟩, hn⟩ := hp'
  have hv : Z4.val I s p = (p.a : ℂ) + (p.b : ℂ) * I := by simp [Z4.val, hc, hd]
  rw [hv] at heq
  have hnorm : Complex.normSq u = ((p.a ^ 2 + p.b ^ 2 : ℚ) : ℝ) := by
    rw [heq]; simp [Complex.normSq_apply, sq]
  rw [h1] at hnorm
  rcases hn with (hn | hn) | hn
  · rw [hn] at hnorm; norm_num at hnorm
  · rcases mul_eq_zero.mp hab with ha | hb
    · have hb2 : (p.b - 1) * (p.b + 1) = 0 := by rw [ha] at hn; linear_combination hn
      rcases mul_eq_zero.mp hb2 with hb | hb
      · have : p.b = 1 := by linarith
        apply hpi; rw [heq, ha, this]; simp
      · have : p.b = -1 := by linarith
        apply hmi; rw [heq, ha, this]; simp
    · have ha2 : (p.a - 1) * (p.a + 1) = 0 := by rw [hb] at hn; linear_combination hn
      rcases mul_eq_zero.mp ha2 with ha | ha
      · have : p.a = 1 := by linarith
        apply hp1; rw [heq, hb, this]; simp
      · have : p.a = -1 := by linarith
        apply hm1; rw [heq, hb, this]; simp
  · have : (4 : ℝ) ≤ ((p.a ^ 2 + p.b ^ 2 : ℚ) : ℝ) := by exact_mod_cast hn
    rw [← hnorm] at this; norm_num at this

open Complex in
/-- För `r = i` och `|u| = 1` är `Q(u) ≠ 0`, så `eul_ne_zero_at_2` gäller för alla `u` på enhetscirkeln. -/
theorem hQ_unit (u : ℂ) (h1 : Complex.normSq u = 1) :
    (u - 4 * I) * (u ^ 2 + (-32/17 + 8/17 * I) * u - 4 * I) ≠ 0 := by
  have h1' := h1
  simp only [Complex.normSq_apply] at h1'
  refine mul_ne_zero ?_ ?_
  · intro h
    rw [sub_eq_zero.mp h] at h1
    simp [Complex.normSq_apply] at h1; norm_num at h1
  · intro h
    have e : u * (u + (-32/17 + 8/17 * I)) = 4 * I := by linear_combination h
    have := congrArg Complex.normSq e
    rw [map_mul, h1, one_mul] at this
    simp [Complex.normSq_apply] at this
    nlinarith [sq_nonneg (16 * u.re + 64 * u.im), sq_nonneg (64 * u.re - 16 * u.im)]

end C488u
end LeanResidy.X
