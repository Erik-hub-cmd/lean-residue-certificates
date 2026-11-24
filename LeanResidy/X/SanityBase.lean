import LeanResidy.SanityBase
import LeanResidy.X.Case

/-!
# Generiska rimlighetssatser för ramverket `LeanResidy.X` (granskning 2026-11-24, kväll)

Skrivna i granskningen, inte av den som skrev resten av koden. Samma roll som `LeanResidy.SanityBase`
och `Sanity<fall>.lean` för de åtta första fallen: satser som visar att huvudsatserna `adjugate`,
`curve`, `partial_fractions` inte är innehållslösa och att datan hänger ihop som artikeln säger.

Allt här gäller för ett godtyckligt datapaket `c : Case K` och en godtycklig sund tolkning `vK`.
-/

set_option linter.unusedSectionVars false

namespace LeanResidy
namespace X
open LeanResidy.Comp

namespace Case
variable {K : Type} [Comp K] (c : Case K)

/-- exponentdatat: `x = v^T` som listor -/
def exOK : Bool :=
  c.ev1.length == c.ev2.length &&
    c.ex1 == List.zipWith (fun u w => c.t00 * u + c.t10 * w) c.ev1 c.ev2 &&
    c.ex2 == List.zipWith (fun u w => c.t01 * u + c.t11 * w) c.ev1 c.ev2

/-- formen på partialbråken: ingen polynomdel, och bara enkla poler i `0` -/
def shapeOK : Bool :=
  c.PFinfL.all (fun l => l.isEmpty) &&
    c.PFfinL.all (fun f => f.all fun t => t.1 != c.iz || t.2.1 == 1)

variable [CInv K]

/-- `v₂∂_{v₂}D^T(v(z))` i punkten `z = q`, exakt i modellen -/
def eulAt (q : ℚ) : K :=
  let ws := c.wsAt q
  let wis := ws.map CInv.inv
  levK id (eulK c.DT) (pvP ws wis c.ev1) (pvP ws wis (c.ev1.map (- ·))) (pvP ws wis c.ev2)
    (pvP ws wis (c.ev2.map (- ·)))

end Case

section
variable {K : Type} [Comp K] {F : Type} [Field F] [CharZero F] (c : Case K) {vK : K → F}

theorem Case.ex_facts (h : c.exOK = true) : c.ev1.length = c.ev2.length ∧
    c.ex1 = List.zipWith (fun u w => c.t00 * u + c.t10 * w) c.ev1 c.ev2 ∧
    c.ex2 = List.zipWith (fun u w => c.t01 * u + c.t11 * w) c.ev1 c.ev2 := by
  simp only [Case.exOK, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **`x = v^T`.** Parametriseringen i `x`-koordinater (Sats B) och i `v`-koordinater (Sats C) är
samma: `x₁ = v₁^{t₀₀} v₂^{t₁₀}`, `x₂ = v₁^{t₀₁} v₂^{t₁₁}`. -/
theorem x_eq_vT_gen (h : c.exOK = true) (z : F) (hz : ∀ q ∈ qv vK c, z ≠ q) :
    xpar (qv vK c) c.ex1 z = xpar (qv vK c) c.ev1 z ^ c.t00 * xpar (qv vK c) c.ev2 z ^ c.t10 ∧
    xpar (qv vK c) c.ex2 z = xpar (qv vK c) c.ev1 z ^ c.t01 * xpar (qv vK c) c.ev2 z ^ c.t11 := by
  obtain ⟨hl, h1, h2⟩ := c.ex_facts h
  constructor
  · conv_lhs => rw [h1]
    exact xpar_lin _ z hz _ _ _ _ hl
  · conv_lhs => rw [h2]
    exact xpar_lin _ z hz _ _ _ _ hl

/-- **Kurvan i `v`-koordinater**, `D^T(v(z)) = 0`, ur Sats B. -/
theorem curve_v_gen (h : c.exOK = true) (z : F) (hz : ∀ q ∈ qv vK c, z ≠ q)
    (hB : levalK vK c.D (xpar (qv vK c) c.ex1 z) (xpar (qv vK c) c.ex2 z) = 0) :
    levalK vK c.DT (xpar (qv vK c) c.ev1 z) (xpar (qv vK c) c.ev2 z) = 0 := by
  rw [Case.DT, levalK_trLK _ _ _ _ _ _ _ _ (xpar_ne_zero _ z hz _) (xpar_ne_zero _ z hz _),
    ← (x_eq_vT_gen c h z hz).1, ← (x_eq_vT_gen c h z hz).2]
  exact hB

theorem pinf_nil_gen (h : c.shapeOK = true) (k l : ℕ) : c.pinf k l = [] := by
  simp only [Case.shapeOK, Bool.and_eq_true, List.all_eq_true] at h
  unfold Case.pinf
  rw [List.getD_eq_getElem?_getD]
  rcases hget : c.PFinfL[k * c.V + l]? with _ | f
  · simp
  · simpa using h.1 f (List.mem_of_getElem? hget)

theorem pfin_zero_simple_gen (h : c.shapeOK = true) (k l : ℕ) :
    ∀ t ∈ c.pfin k l, t.1 = c.iz → t.2.1 = 1 := by
  simp only [Case.shapeOK, Bool.and_eq_true, List.all_eq_true] at h
  intro t ht h0
  unfold Case.pfin at ht
  rw [List.getD_eq_getElem?_getD] at ht
  rcases hget : c.PFfinL[k * c.V + l]? with _ | f
  · simp [hget] at ht
  · rw [hget, Option.getD_some] at ht
    have := h.2 f (List.mem_of_getElem? hget) t ht
    simpa [h0] using this

/-- **Inversen av laplacianen** ur Sats A: där `D ≠ 0` är `M(x)⁻¹ = D⁻¹ • A(x)`. -/
theorem green_gen (x1 x2 : F)
    (hA : lapMatK vK c.V c.E x1 x2 * lmatK vK c.V c.A x1 x2 =
      levalK vK c.D x1 x2 • (1 : Matrix (Fin c.V) (Fin c.V) F))
    (hD : levalK vK c.D x1 x2 ≠ 0) :
    (lapMatK vK c.V c.E x1 x2)⁻¹ = (levalK vK c.D x1 x2)⁻¹ • lmatK vK c.V c.A x1 x2 := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.mul_smul, hA, smul_smul, inv_mul_cancel₀ hD, one_smul]

/-- **Sats C som likhet för integranden** (ingen polynomdel): där nämnaren är ≠ 0 är
`ρ_{kl}(z)` exakt partialbråket. -/
theorem integrand_gen (hs : c.shapeOK = true) (k l : Fin c.V) (z : F)
    (hC : levalK vK (c.A k l) (xpar (qv vK c) c.ex1 z) (xpar (qv vK c) c.ex2 z) *
        dlogv (qv vK c) c.ev1 z =
      levalK vK (eulK c.DT) (xpar (qv vK c) c.ev1 z) (xpar (qv vK c) c.ev2 z) *
        pfval (qv vK c) ((c.pfin k l).map fun t => (t.1, t.2.1, vK t.2.2))
          ((c.pinf k l).map fun t => (t.1, vK t.2)) z)
    (hE : levalK vK (eulK c.DT) (xpar (qv vK c) c.ev1 z) (xpar (qv vK c) c.ev2 z) ≠ 0) :
    levalK vK (c.A k l) (xpar (qv vK c) c.ex1 z) (xpar (qv vK c) c.ex2 z) *
        dlogv (qv vK c) c.ev1 z / levalK vK (eulK c.DT) (xpar (qv vK c) c.ev1 z) (xpar (qv vK c) c.ev2 z) =
      pfval (qv vK c) ((c.pfin k l).map fun t => (t.1, t.2.1, vK t.2.2)) [] z := by
  rw [div_eq_iff hE, hC, pinf_nil_gen c hs, List.map_nil]
  ring

/-! ### Nämnaren i en kontrollpunkt -/

variable (S : Sound vK) [CInv K]
include S

theorem okAt_hw' (q : ℚ) (i : ℕ) (hi : i < (qv vK c).length) :
    vK ((c.wsAt q).getD i Comp.zero) = (q : F) - (qv vK c).getD i 0 := by
  simp only [qv, List.length_map] at hi
  simp [Case.wsAt, qv, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
    S.add, S.neg, S.ofQ, sub_eq_add_neg]

theorem okAt_inv' (q : ℚ) (h : c.okAt q = true) (i : ℕ) (hi : i < (c.wsAt q).length) :
    vK (CInv.inv (c.wsAt q)[i]) = (vK (c.wsAt q)[i])⁻¹ ∧ vK (c.wsAt q)[i] ≠ 0 := by
  simp only [Case.okAt, List.all_eq_true] at h
  exact val_invOK S _ _ (h _ (List.getElem_mem hi))

theorem okAt_hwi' (q : ℚ) (h : c.okAt q = true) (i : ℕ) (hi : i < (qv vK c).length) :
    vK (((c.wsAt q).map CInv.inv).getD i Comp.zero) = ((q : F) - (qv vK c).getD i 0)⁻¹ := by
  have hi' : i < (c.wsAt q).length := by simpa [Case.wsAt, qv] using hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi',
    Option.map_some, Option.getD_some, (okAt_inv' c S q h i hi').1,
    ← okAt_hw' c S q i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi',
    Option.getD_some]

theorem okAt_nonpunct' (q : ℚ) (h : c.okAt q = true) : ∀ p ∈ qv vK c, (q : F) ≠ p := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  have hw := okAt_hw' c S q i hi
  have hi' : i < (c.wsAt q).length := by simpa [Case.wsAt, qv] using hi
  have hne := (okAt_inv' c S q h i hi').2
  have hg : (c.wsAt q).getD i Comp.zero = (c.wsAt q)[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
  rw [← hg] at hne
  intro heq
  apply hne
  rw [hw, sub_eq_zero, heq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

/-- Värdet av modellräkningen `eulAt q` är nämnaren `v₂∂_{v₂}D^T(v(q))`. -/
theorem val_eulAt (q : ℚ) (hok : c.okAt q = true) :
    vK (c.eulAt q) = levalK vK (eulK c.DT) (xpar (qv vK c) c.ev1 (q : F)) (xpar (qv vK c) c.ev2 (q : F)) := by
  have hw := okAt_hw' c S q
  have hwi := okAt_hwi' c S q hok
  have hzc : ∀ p ∈ qv vK c, (q : F) ≠ p := okAt_nonpunct' c S q hok
  have hl1 : (c.wsAt q).length = (qv vK c).length := by simp [Case.wsAt, qv]
  have hl2 : ((c.wsAt q).map CInv.inv).length = (qv vK c).length := by simp [Case.wsAt, qv]
  have P := fun es => val_pvP S (qv vK c) (q : F) (c.wsAt q) ((c.wsAt q).map CInv.inv) hl1 hl2
    hw hwi es
  have hid : ∀ k : K, vK (id k) = vK k := fun _ => rfl
  simp only [Case.eulAt]
  rw [val_levK S vK id hid _ _ _ _ _ (by rw [P, P, pe_neg _ _ hzc]) (by rw [P, P, pe_neg _ _ hzc]),
    P, P]
  simp only [xpar_eq_pe]

/-- Om `eulAt q · wi = 1` i modellen (för ett valfritt `wi`), är nämnaren ≠ 0 i `z = q`. -/
theorem eul_ne_zero_gen (q : ℚ) (wi : K) (hok : c.okAt q = true) (hinv : invOK (c.eulAt q) wi = true) :
    levalK vK (eulK c.DT) (xpar (qv vK c) c.ev1 (q : F)) (xpar (qv vK c) c.ev2 (q : F)) ≠ 0 := by
  rw [← val_eulAt c S q hok]
  exact (val_invOK S _ _ hinv).2

end

end X
end LeanResidy
