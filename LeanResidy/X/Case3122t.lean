import LeanResidy.X.Data3122t

/-!
# 3.12² med vikt t på 12–12-kanterna (artikel 3, Sats thm:3122t): maskinkontrollerade identiteter (generiska ramverket `LeanResidy.X`)

Datat finns i `Data3122t.lean`; satserna följer ur `adjugate_gen`, `curve_gen` och
`partial_fractions_gen` i `X/Case.lean` sedan kärnan räknat ut kontrollerna nedan.
-/

set_option linter.unusedSectionVars false

set_option Elab.async false

namespace LeanResidy.X
namespace C3122t
open LeanResidy.Comp

/-! ## Kärnans räkningar -/

theorem adj_0_0 : data.adjEnt 0 0 = true := by decide +kernel
theorem adj_0_1 : data.adjEnt 0 1 = true := by decide +kernel
theorem adj_0_2 : data.adjEnt 0 2 = true := by decide +kernel
theorem adj_0_3 : data.adjEnt 0 3 = true := by decide +kernel
theorem adj_0_4 : data.adjEnt 0 4 = true := by decide +kernel
theorem adj_0_5 : data.adjEnt 0 5 = true := by decide +kernel
theorem adj_0 : data.adjRow 0 = true := data.adjRow_of 0 (by
  intro k hk; simp only [data] at hk; interval_cases k
  · exact adj_0_0
  · exact adj_0_1
  · exact adj_0_2
  · exact adj_0_3
  · exact adj_0_4
  · exact adj_0_5
  )
theorem adj_1_0 : data.adjEnt 1 0 = true := by decide +kernel
theorem adj_1_1 : data.adjEnt 1 1 = true := by decide +kernel
theorem adj_1_2 : data.adjEnt 1 2 = true := by decide +kernel
theorem adj_1_3 : data.adjEnt 1 3 = true := by decide +kernel
theorem adj_1_4 : data.adjEnt 1 4 = true := by decide +kernel
theorem adj_1_5 : data.adjEnt 1 5 = true := by decide +kernel
theorem adj_1 : data.adjRow 1 = true := data.adjRow_of 1 (by
  intro k hk; simp only [data] at hk; interval_cases k
  · exact adj_1_0
  · exact adj_1_1
  · exact adj_1_2
  · exact adj_1_3
  · exact adj_1_4
  · exact adj_1_5
  )
theorem adj_2_0 : data.adjEnt 2 0 = true := by decide +kernel
theorem adj_2_1 : data.adjEnt 2 1 = true := by decide +kernel
theorem adj_2_2 : data.adjEnt 2 2 = true := by decide +kernel
theorem adj_2_3 : data.adjEnt 2 3 = true := by decide +kernel
theorem adj_2_4 : data.adjEnt 2 4 = true := by decide +kernel
theorem adj_2_5 : data.adjEnt 2 5 = true := by decide +kernel
theorem adj_2 : data.adjRow 2 = true := data.adjRow_of 2 (by
  intro k hk; simp only [data] at hk; interval_cases k
  · exact adj_2_0
  · exact adj_2_1
  · exact adj_2_2
  · exact adj_2_3
  · exact adj_2_4
  · exact adj_2_5
  )
theorem adj_3_0 : data.adjEnt 3 0 = true := by decide +kernel
theorem adj_3_1 : data.adjEnt 3 1 = true := by decide +kernel
theorem adj_3_2 : data.adjEnt 3 2 = true := by decide +kernel
theorem adj_3_3 : data.adjEnt 3 3 = true := by decide +kernel
theorem adj_3_4 : data.adjEnt 3 4 = true := by decide +kernel
theorem adj_3_5 : data.adjEnt 3 5 = true := by decide +kernel
theorem adj_3 : data.adjRow 3 = true := data.adjRow_of 3 (by
  intro k hk; simp only [data] at hk; interval_cases k
  · exact adj_3_0
  · exact adj_3_1
  · exact adj_3_2
  · exact adj_3_3
  · exact adj_3_4
  · exact adj_3_5
  )
theorem adj_4_0 : data.adjEnt 4 0 = true := by decide +kernel
theorem adj_4_1 : data.adjEnt 4 1 = true := by decide +kernel
theorem adj_4_2 : data.adjEnt 4 2 = true := by decide +kernel
theorem adj_4_3 : data.adjEnt 4 3 = true := by decide +kernel
theorem adj_4_4 : data.adjEnt 4 4 = true := by decide +kernel
theorem adj_4_5 : data.adjEnt 4 5 = true := by decide +kernel
theorem adj_4 : data.adjRow 4 = true := data.adjRow_of 4 (by
  intro k hk; simp only [data] at hk; interval_cases k
  · exact adj_4_0
  · exact adj_4_1
  · exact adj_4_2
  · exact adj_4_3
  · exact adj_4_4
  · exact adj_4_5
  )
theorem adj_5_0 : data.adjEnt 5 0 = true := by decide +kernel
theorem adj_5_1 : data.adjEnt 5 1 = true := by decide +kernel
theorem adj_5_2 : data.adjEnt 5 2 = true := by decide +kernel
theorem adj_5_3 : data.adjEnt 5 3 = true := by decide +kernel
theorem adj_5_4 : data.adjEnt 5 4 = true := by decide +kernel
theorem adj_5_5 : data.adjEnt 5 5 = true := by decide +kernel
theorem adj_5 : data.adjRow 5 = true := data.adjRow_of 5 (by
  intro k hk; simp only [data] at hk; interval_cases k
  · exact adj_5_0
  · exact adj_5_1
  · exact adj_5_2
  · exact adj_5_3
  · exact adj_5_4
  · exact adj_5_5
  )
theorem curve_ok : data.curveCheck = true := by decide +kernel
theorem idx_ok : data.idxCheck = true := by decide +kernel
theorem deg_0 : data.degRow 0 = true := by decide +kernel
theorem deg_1 : data.degRow 1 = true := by decide +kernel
theorem deg_2 : data.degRow 2 = true := by decide +kernel
theorem deg_3 : data.degRow 3 = true := by decide +kernel
theorem deg_4 : data.degRow 4 = true := by decide +kernel
theorem deg_5 : data.degRow 5 = true := by decide +kernel

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

theorem adj_all : ∀ i < data.V, data.adjRow i = true := by
  intro i hi; simp only [data] at hi; interval_cases i
  · exact adj_0
  · exact adj_1
  · exact adj_2
  · exact adj_3
  · exact adj_4
  · exact adj_5

theorem deg_all : ∀ i < data.V, data.degRow i = true := by
  intro i hi; simp only [data] at hi; interval_cases i
  · exact deg_0
  · exact deg_1
  · exact deg_2
  · exact deg_3
  · exact deg_4
  · exact deg_5

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

/-! ## Satserna

Koefficienterna ligger i `K` = rationella funktioner i parametern `u` (se datafilen) över `ℚ(r, s)`,
`r² = -3`, `s² = -1`. Satserna gäller för **varje** `u` i en kropp `F` av karakteristik 0 utanför de
ändligt många punkterna `tpts` (nämnarnas nollställen och, för kontrollpunkterna, de `u` där en
kontrollpunkt z = 2, 3, … skulle vara en punktering), och för varje val av rötterna `r`, `s`.
-/

variable {F : Type} [Field F] [CharZero F] (r s u : F)

/-- tolkningen av `K`: värdet i parametern `u` -/
def vK : K → F := Fr.val (Z4.val r s) u

section
variable (hr : r ^ 2 = ((-3 : ℤ) : F)) (hs : s ^ 2 = ((-1 : ℤ) : F))
  (hu : ∀ p ∈ tpts, u ≠ Z4.val r s p)
include hr hs hu

theorem sound : Sound (vK r s u) := Fr.sound (Z4.sound r s hr hs) u hu


/-- **Sats A (adjunkten).** `M(x)·A(x) = D(x)·I` för alla `x₁, x₂ ≠ 0`. -/
theorem adjugate (x1 x2 : F) (h1 : x1 ≠ 0) (h2 : x2 ≠ 0) :
    lapMatK (vK r s u) data.V data.E x1 x2 * lmatK (vK r s u) data.V data.A x1 x2 =
      levalK (vK r s u) data.D x1 x2 • (1 : Matrix (Fin data.V) (Fin data.V) F) :=
  adjugate_gen data (sound r s u hr hs hu) adj_all x1 x2 h1 h2

/-- **Sats B (kurvan).** `D(x(z)) = 0` för alla `z` utanför punkteringarna. -/
theorem curve (z : F) (hz : ∀ q ∈ qv (vK r s u) data, z ≠ q) :
    levalK (vK r s u) data.D (xpar (qv (vK r s u) data) data.ex1 z)
      (xpar (qv (vK r s u) data) data.ex2 z) = 0 :=
  curve_gen data (sound r s u hr hs hu) curve_ok z hz

/-- **Sats C (partialbråken)** för alla `V²` poster. -/
theorem partial_fractions (k l : Fin data.V) (z : F) (hz : ∀ q ∈ qv (vK r s u) data, z ≠ q) :
    levalK (vK r s u) (data.A k l) (xpar (qv (vK r s u) data) data.ex1 z)
        (xpar (qv (vK r s u) data) data.ex2 z) * dlogv (qv (vK r s u) data) data.ev1 z =
      levalK (vK r s u) (eulK data.DT) (xpar (qv (vK r s u) data) data.ev1 z)
          (xpar (qv (vK r s u) data) data.ev2 z) *
        pfval (qv (vK r s u) data) ((data.pfin k l).map fun t' => (t'.1, t'.2.1, vK r s u t'.2.2))
          ((data.pinf k l).map fun t' => (t'.1, vK r s u t'.2)) z :=
  partial_fractions_gen data (sound r s u hr hs hu) idx_ok deg_all pt_all k l z hz

end

end C3122t
end LeanResidy.X
