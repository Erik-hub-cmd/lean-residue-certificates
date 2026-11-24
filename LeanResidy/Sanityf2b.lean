import LeanResidy.SanityBase
import LeanResidy.Casef2b

/-!
# Rimlighetssatser för fallet f2b (granskning 2026-11-24)

Satser som visar att huvudsatserna `adjugate`, `curve`, `partial_fractions` inte är innehållslösa och
att data hänger ihop som artikeln säger. Skrivna i granskningen, inte av den som skrev resten av koden.
-/

namespace LeanResidy
namespace Cf2b
open LeanResidy.Comp

/-- `T` ligger i `SL₂(ℤ)`. -/
theorem T_det : t00 * t11 - t01 * t10 = 1 := by decide

/-- Exponentdata: `x` och `v` hänger ihop via `T`, dvs. `x₁ = v₁^{t₀₀} v₂^{t₁₀}`, `x₂ = v₁^{t₀₁} v₂^{t₁₁}`. -/
theorem ex_data : ev1.length = ev2.length ∧
    ex1 = List.zipWith (fun u w => t00 * u + t10 * w) ev1 ev2 ∧
    ex2 = List.zipWith (fun u w => t01 * u + t11 * w) ev1 ev2 := by decide

/-- Polerna i ∞ och i 0: inga polynomdelar, och bara enkla poler i 0. -/
theorem pf_shape_data : PFinfL.all (fun l => l.isEmpty) = true ∧
    PFfinL.all (fun f => f.all fun t => t.1 != iz || t.2.1 == 1) = true := by decide +kernel

theorem pinf_nil (k l : ℕ) : pinf k l = [] := by
  have h := pf_shape_data.1
  simp only [List.all_eq_true] at h
  unfold pinf
  rw [List.getD_eq_getElem?_getD]
  rcases hget : PFinfL[k * V + l]? with _ | f
  · simp
  · simpa using h f (List.mem_of_getElem? hget)

theorem pfin_zero_simple (k l : ℕ) : ∀ t ∈ pfin k l, t.1 = iz → t.2.1 = 1 := by
  have h := pf_shape_data.2
  simp only [List.all_eq_true] at h
  intro t ht h0
  unfold pfin at ht
  rw [List.getD_eq_getElem?_getD] at ht
  rcases hget : PFfinL[k * V + l]? with _ | f
  · simp [hget] at ht
  · rw [hget, Option.getD_some] at ht
    have := h f (List.mem_of_getElem? hget) t ht
    simpa [h0] using this

/-- `D` är inte nollpolynomet (värdet i (2, 3) är ≠ 0), så `M·A = D·I` säger att `M(x)` är
inverterbar med invers `A/D` för generiska `x`. -/
theorem D_ne_zero_Q : leval D (2 : ℚ) 3 ≠ 0 := by decide +kernel

variable {F : Type} [Field F] [CharZero F]

theorem D_ne_zero : leval D (2 : F) 3 ≠ 0 := by
  have h := leval_cast (F := F) D 2 3
  push_cast at h
  rw [h]; exact_mod_cast D_ne_zero_Q

/-- Konsekvens av `adjugate`: i en punkt där `D ≠ 0` är `M(x)` inverterbar och `M(x)⁻¹ = D⁻¹ • A(x)`. -/
theorem green (x1 x2 : F) (h1 : x1 ≠ 0) (h2 : x2 ≠ 0) (hD : leval D x1 x2 ≠ 0) :
    (lapMat V E x1 x2)⁻¹ = (leval D x1 x2)⁻¹ • lmat V A x1 x2 := by
  have h := adjugate x1 x2 h1 h2
  apply Matrix.inv_eq_right_inv
  rw [Matrix.mul_smul, h, smul_smul, inv_mul_cancel₀ hD, one_smul]

/-- kontrollen att nämnaren `v₂∂_{v₂}D^T` är ≠ 0 i `z = 2` (exakt i ℚ(r, s)) -/
def eulAt2 : K :=
  let ws := wsAt pts 2
  let wis := ws.map Z4.inv
  lev (eul DT) (pvP ws wis ev1) (pvP ws wis (ev1.map (- ·))) (pvP ws wis ev2) (pvP ws wis (ev2.map (- ·)))

theorem eulAt2_ok : okAt pts 2 = true ∧ Z4.okInv eulAt2 = true := by decide +kernel

section
variable (r s : F) (hr : r ^ 2 = KA) (hs : s ^ 2 = KB)
include hr hs

omit [CharZero F] hr hs in
/-- Parametriseringen i `v`-koordinater: `x = v^T` för varje `z` utanför punkteringarna. -/
theorem x_eq_vT (z : F) (hz : ∀ q ∈ qv r s, z ≠ q) :
    xpar (qv r s) ex1 z = xpar (qv r s) ev1 z ^ t00 * xpar (qv r s) ev2 z ^ t10 ∧
    xpar (qv r s) ex2 z = xpar (qv r s) ev1 z ^ t01 * xpar (qv r s) ev2 z ^ t11 := by
  obtain ⟨hl, h1, h2⟩ := ex_data
  constructor
  · conv_lhs => rw [h1]
    exact xpar_lin _ z hz _ _ _ _ hl
  · conv_lhs => rw [h2]
    exact xpar_lin _ z hz _ _ _ _ hl

/-- Kurvan i `v`-koordinater: `D^T(v(z)) = 0`. (Det är `D^T` vars `v₂`-derivata står i Sats C.) -/
theorem curve_v (z : F) (hz : ∀ q ∈ qv r s, z ≠ q) :
    leval DT (xpar (qv r s) ev1 z) (xpar (qv r s) ev2 z) = 0 := by
  rw [DT, leval_trL _ _ _ _ _ _ _ (xpar_ne_zero _ z hz _) (xpar_ne_zero _ z hz _),
    ← (x_eq_vT r s z hz).1, ← (x_eq_vT r s z hz).2]
  exact curve r s hr hs z hz

/-- Nämnaren `v₂∂_{v₂}D^T(v(z))` är inte identiskt noll längs parametriseringen (≠ 0 i `z = 2`). -/
theorem eul_ne_zero_at_2 :
    leval (eul DT) (xpar (qv r s) ev1 ((2 : ℚ) : F)) (xpar (qv r s) ev2 ((2 : ℚ) : F)) ≠ 0 := by
  have S4 := Z4.sound r s hr hs
  obtain ⟨hok, hinv⟩ := eulAt2_ok
  have hw := okAt_hw r s hr hs pts 2
  have hwi := okAt_hwi r s hr hs pts 2 hok
  have hzc : ∀ q ∈ qv r s, ((2 : ℚ) : F) ≠ q := okAt_nonpunct r s hr hs pts 2 hok
  have hl1 : (wsAt pts 2).length = (qv r s).length := by simp [wsAt, qv]
  have hl2 : ((wsAt pts 2).map Z4.inv).length = (qv r s).length := by simp [wsAt, qv]
  have P := fun es => val_pvP S4 (qv r s) ((2 : ℚ) : F) (wsAt pts 2) ((wsAt pts 2).map Z4.inv)
    hl1 hl2 hw hwi es
  have h := Z4.val_ne_zero' r s hr hs _ hinv
  simp only [eulAt2] at h
  rw [val_lev S4 _ _ _ _ _ (by rw [P, P, pe_neg _ _ hzc]) (by rw [P, P, pe_neg _ _ hzc]), P, P] at h
  simpa only [xpar_eq_pe] using h

/-- **Sats C som likhet för integranden.** Där nämnaren är ≠ 0 är
`ρ_{kl}(z) = A_{kl}(x(z)) · (v₁'/v₁)(z) / (v₂∂_{v₂}D^T)(v(z))` exakt partialbråket `PF_{kl}(z)`,
som har formen `Σ c/(z − qᵢ)^m` (ingen polynomdel, enkel pol i 0; `pinf_nil`, `pfin_zero_simple`). -/
theorem integrand (k l : Fin V) (z : F) (hz : ∀ q ∈ qv r s, z ≠ q)
    (hE : leval (eul DT) (xpar (qv r s) ev1 z) (xpar (qv r s) ev2 z) ≠ 0) :
    leval (A k l) (xpar (qv r s) ex1 z) (xpar (qv r s) ex2 z) * dlogv (qv r s) ev1 z /
        leval (eul DT) (xpar (qv r s) ev1 z) (xpar (qv r s) ev2 z) =
      pfval (qv r s) ((pfin k l).map fun t => (t.1, t.2.1, Z4.val r s t.2.2)) [] z := by
  rw [div_eq_iff hE, partial_fractions r s hr hs k l z hz, pinf_nil, List.map_nil]
  ring

end

end Cf2b
end LeanResidy
