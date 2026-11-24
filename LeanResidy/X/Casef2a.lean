import LeanResidy.X.Dataf2a

/-!
# [3².6²; 3.6.3.6] med lika vikter (artikel 3, Fa; nämnd i artikel 2): maskinkontrollerade identiteter (generiska ramverket `LeanResidy.X`)

Datat finns i `Dataf2a.lean`; satserna följer ur `adjugate_gen`, `curve_gen` och
`partial_fractions_gen` i `X/Case.lean` sedan kärnan räknat ut kontrollerna nedan.
-/

set_option linter.unusedSectionVars false

set_option Elab.async false

namespace LeanResidy.X
namespace Cf2a
open LeanResidy.Comp

/-! ## Kärnans räkningar -/

theorem adj_0_0 : data.adjEnt 0 0 = true := by decide +kernel
theorem adj_0_1 : data.adjEnt 0 1 = true := by decide +kernel
theorem adj_0_2 : data.adjEnt 0 2 = true := by decide +kernel
theorem adj_0 : data.adjRow 0 = true := data.adjRow_of 0 (by
  intro k hk; simp only [data] at hk; interval_cases k
  · exact adj_0_0
  · exact adj_0_1
  · exact adj_0_2
  )
theorem adj_1_0 : data.adjEnt 1 0 = true := by decide +kernel
theorem adj_1_1 : data.adjEnt 1 1 = true := by decide +kernel
theorem adj_1_2 : data.adjEnt 1 2 = true := by decide +kernel
theorem adj_1 : data.adjRow 1 = true := data.adjRow_of 1 (by
  intro k hk; simp only [data] at hk; interval_cases k
  · exact adj_1_0
  · exact adj_1_1
  · exact adj_1_2
  )
theorem adj_2_0 : data.adjEnt 2 0 = true := by decide +kernel
theorem adj_2_1 : data.adjEnt 2 1 = true := by decide +kernel
theorem adj_2_2 : data.adjEnt 2 2 = true := by decide +kernel
theorem adj_2 : data.adjRow 2 = true := data.adjRow_of 2 (by
  intro k hk; simp only [data] at hk; interval_cases k
  · exact adj_2_0
  · exact adj_2_1
  · exact adj_2_2
  )
theorem curve_ok : data.curveCheck = true := by decide +kernel
theorem idx_ok : data.idxCheck = true := by decide +kernel
theorem deg_0 : data.degRow 0 = true := by decide +kernel
theorem deg_1 : data.degRow 1 = true := by decide +kernel
theorem deg_2 : data.degRow 2 = true := by decide +kernel

def PT (j : ℕ) : Bool := data.pointOK ((j : ℚ) + 2)
theorem pt_0 : PT 0 = true := by decide +kernel
theorem pt_1 : PT 1 = true := by decide +kernel
theorem pt_2 : PT 2 = true := by decide +kernel
theorem pt_3 : PT 3 = true := by decide +kernel
theorem pt_4 : PT 4 = true := by decide +kernel
theorem pt_5 : PT 5 = true := by decide +kernel
theorem pt_6 : PT 6 = true := by decide +kernel
theorem pt_7 : PT 7 = true := by decide +kernel
theorem pt_8 : PT 8 = true := by decide +kernel
theorem pt_9 : PT 9 = true := by decide +kernel
theorem pt_10 : PT 10 = true := by decide +kernel
theorem pt_11 : PT 11 = true := by decide +kernel
theorem pt_12 : PT 12 = true := by decide +kernel
theorem pt_13 : PT 13 = true := by decide +kernel
theorem pt_14 : PT 14 = true := by decide +kernel

theorem adj_all : ∀ i < data.V, data.adjRow i = true := by
  intro i hi; simp only [data] at hi; interval_cases i
  · exact adj_0
  · exact adj_1
  · exact adj_2

theorem deg_all : ∀ i < data.V, data.degRow i = true := by
  intro i hi; simp only [data] at hi; interval_cases i
  · exact deg_0
  · exact deg_1
  · exact deg_2

theorem pt_all : ∀ j < data.dmax + 1, data.pointOK ((j : ℚ) + 2) = true := by
  intro j hj; simp only [data] at hj
  show PT j = true
  interval_cases j
  · exact pt_0
  · exact pt_1
  · exact pt_2
  · exact pt_3
  · exact pt_4
  · exact pt_5
  · exact pt_6
  · exact pt_7
  · exact pt_8
  · exact pt_9
  · exact pt_10
  · exact pt_11
  · exact pt_12
  · exact pt_13
  · exact pt_14

/-! ## Satserna

Kroppen `K = ℚ(r, s, t)`, `r² = A`, `s² = B`, `t² = C` (se `K` i datafilen). Satserna gäller för
**varje** val av kvadratrötter `r, s, t` i en kropp `F` av karakteristik 0, alltså för alla åtta
Galoiskonjugat av parametriseringen samtidigt.
-/

variable {F : Type} [Field F] [CharZero F] (r s t : F)

/-- tolkningen av `K` -/
def vK : K → F := Z8.val r s t

section
variable (hr : r ^ 2 = ((-1 : ℤ) : F)) (hs : s ^ 2 = ((2 : ℤ) : F)) (ht : t ^ 2 = ((3 : ℚ) : F))
include hr hs ht

theorem sound : Sound (vK r s t) := Z8.sound r s t hr hs ht


/-- **Sats A (adjunkten).** `M(x)·A(x) = D(x)·I` för alla `x₁, x₂ ≠ 0`. -/
theorem adjugate (x1 x2 : F) (h1 : x1 ≠ 0) (h2 : x2 ≠ 0) :
    lapMatK (vK r s t) data.V data.E x1 x2 * lmatK (vK r s t) data.V data.A x1 x2 =
      levalK (vK r s t) data.D x1 x2 • (1 : Matrix (Fin data.V) (Fin data.V) F) :=
  adjugate_gen data (sound r s t hr hs ht) adj_all x1 x2 h1 h2

/-- **Sats B (kurvan).** `D(x(z)) = 0` för alla `z` utanför punkteringarna. -/
theorem curve (z : F) (hz : ∀ q ∈ qv (vK r s t) data, z ≠ q) :
    levalK (vK r s t) data.D (xpar (qv (vK r s t) data) data.ex1 z)
      (xpar (qv (vK r s t) data) data.ex2 z) = 0 :=
  curve_gen data (sound r s t hr hs ht) curve_ok z hz

/-- **Sats C (partialbråken)** för alla `V²` poster. -/
theorem partial_fractions (k l : Fin data.V) (z : F) (hz : ∀ q ∈ qv (vK r s t) data, z ≠ q) :
    levalK (vK r s t) (data.A k l) (xpar (qv (vK r s t) data) data.ex1 z)
        (xpar (qv (vK r s t) data) data.ex2 z) * dlogv (qv (vK r s t) data) data.ev1 z =
      levalK (vK r s t) (eulK data.DT) (xpar (qv (vK r s t) data) data.ev1 z)
          (xpar (qv (vK r s t) data) data.ev2 z) *
        pfval (qv (vK r s t) data) ((data.pfin k l).map fun t' => (t'.1, t'.2.1, vK r s t t'.2.2))
          ((data.pinf k l).map fun t' => (t'.1, vK r s t t'.2)) z :=
  partial_fractions_gen data (sound r s t hr hs ht) idx_ok deg_all pt_all k l z hz

end

end Cf2a
end LeanResidy.X
