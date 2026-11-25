import LeanResidy.X.Dataf2bwK
import LeanResidy.X.KronSanity

/-!
# Maskinkontrollerade identiteter, Kroneckerpackade modellen

Satserna följer ur `adjugate_gen`, `curve_gen_pts` och `partial_fractions_gen` i `X/Case.lean`
med koefficientmodellen `K = FrG (PK A B Kb S) Dl` (`X/Kron.lean`, `X/FrG.lean`).
-/

set_option linter.unusedSectionVars false
set_option Elab.async false

namespace LeanResidy.X
namespace Cf2bwK
open LeanResidy.Comp

/-! ## Kärnans räkningar -/

theorem adj_0_0 : data.adjEnt 0 0 = true := by decide +kernel
theorem adj_0_1 : data.adjEnt 0 1 = true := by decide +kernel
theorem adj_0_2 : data.adjEnt 0 2 = true := by decide +kernel
theorem adj_0_3 : data.adjEnt 0 3 = true := by decide +kernel
theorem adj_0_4 : data.adjEnt 0 4 = true := by decide +kernel
theorem adj_0_5 : data.adjEnt 0 5 = true := by decide +kernel
theorem adj_0_6 : data.adjEnt 0 6 = true := by decide +kernel
theorem adj_0_7 : data.adjEnt 0 7 = true := by decide +kernel
theorem adj_0 : data.adjRow 0 = true := data.adjRow_of 0 (by
  intro k hk; simp only [show data.V = 8 from rfl] at hk; interval_cases k
  · exact adj_0_0
  · exact adj_0_1
  · exact adj_0_2
  · exact adj_0_3
  · exact adj_0_4
  · exact adj_0_5
  · exact adj_0_6
  · exact adj_0_7
  )
theorem adj_1_0 : data.adjEnt 1 0 = true := by decide +kernel
theorem adj_1_1 : data.adjEnt 1 1 = true := by decide +kernel
theorem adj_1_2 : data.adjEnt 1 2 = true := by decide +kernel
theorem adj_1_3 : data.adjEnt 1 3 = true := by decide +kernel
theorem adj_1_4 : data.adjEnt 1 4 = true := by decide +kernel
theorem adj_1_5 : data.adjEnt 1 5 = true := by decide +kernel
theorem adj_1_6 : data.adjEnt 1 6 = true := by decide +kernel
theorem adj_1_7 : data.adjEnt 1 7 = true := by decide +kernel
theorem adj_1 : data.adjRow 1 = true := data.adjRow_of 1 (by
  intro k hk; simp only [show data.V = 8 from rfl] at hk; interval_cases k
  · exact adj_1_0
  · exact adj_1_1
  · exact adj_1_2
  · exact adj_1_3
  · exact adj_1_4
  · exact adj_1_5
  · exact adj_1_6
  · exact adj_1_7
  )
theorem adj_2_0 : data.adjEnt 2 0 = true := by decide +kernel
theorem adj_2_1 : data.adjEnt 2 1 = true := by decide +kernel
theorem adj_2_2 : data.adjEnt 2 2 = true := by decide +kernel
theorem adj_2_3 : data.adjEnt 2 3 = true := by decide +kernel
theorem adj_2_4 : data.adjEnt 2 4 = true := by decide +kernel
theorem adj_2_5 : data.adjEnt 2 5 = true := by decide +kernel
theorem adj_2_6 : data.adjEnt 2 6 = true := by decide +kernel
theorem adj_2_7 : data.adjEnt 2 7 = true := by decide +kernel
theorem adj_2 : data.adjRow 2 = true := data.adjRow_of 2 (by
  intro k hk; simp only [show data.V = 8 from rfl] at hk; interval_cases k
  · exact adj_2_0
  · exact adj_2_1
  · exact adj_2_2
  · exact adj_2_3
  · exact adj_2_4
  · exact adj_2_5
  · exact adj_2_6
  · exact adj_2_7
  )
theorem adj_3_0 : data.adjEnt 3 0 = true := by decide +kernel
theorem adj_3_1 : data.adjEnt 3 1 = true := by decide +kernel
theorem adj_3_2 : data.adjEnt 3 2 = true := by decide +kernel
theorem adj_3_3 : data.adjEnt 3 3 = true := by decide +kernel
theorem adj_3_4 : data.adjEnt 3 4 = true := by decide +kernel
theorem adj_3_5 : data.adjEnt 3 5 = true := by decide +kernel
theorem adj_3_6 : data.adjEnt 3 6 = true := by decide +kernel
theorem adj_3_7 : data.adjEnt 3 7 = true := by decide +kernel
theorem adj_3 : data.adjRow 3 = true := data.adjRow_of 3 (by
  intro k hk; simp only [show data.V = 8 from rfl] at hk; interval_cases k
  · exact adj_3_0
  · exact adj_3_1
  · exact adj_3_2
  · exact adj_3_3
  · exact adj_3_4
  · exact adj_3_5
  · exact adj_3_6
  · exact adj_3_7
  )
theorem adj_4_0 : data.adjEnt 4 0 = true := by decide +kernel
theorem adj_4_1 : data.adjEnt 4 1 = true := by decide +kernel
theorem adj_4_2 : data.adjEnt 4 2 = true := by decide +kernel
theorem adj_4_3 : data.adjEnt 4 3 = true := by decide +kernel
theorem adj_4_4 : data.adjEnt 4 4 = true := by decide +kernel
theorem adj_4_5 : data.adjEnt 4 5 = true := by decide +kernel
theorem adj_4_6 : data.adjEnt 4 6 = true := by decide +kernel
theorem adj_4_7 : data.adjEnt 4 7 = true := by decide +kernel
theorem adj_4 : data.adjRow 4 = true := data.adjRow_of 4 (by
  intro k hk; simp only [show data.V = 8 from rfl] at hk; interval_cases k
  · exact adj_4_0
  · exact adj_4_1
  · exact adj_4_2
  · exact adj_4_3
  · exact adj_4_4
  · exact adj_4_5
  · exact adj_4_6
  · exact adj_4_7
  )
theorem adj_5_0 : data.adjEnt 5 0 = true := by decide +kernel
theorem adj_5_1 : data.adjEnt 5 1 = true := by decide +kernel
theorem adj_5_2 : data.adjEnt 5 2 = true := by decide +kernel
theorem adj_5_3 : data.adjEnt 5 3 = true := by decide +kernel
theorem adj_5_4 : data.adjEnt 5 4 = true := by decide +kernel
theorem adj_5_5 : data.adjEnt 5 5 = true := by decide +kernel
theorem adj_5_6 : data.adjEnt 5 6 = true := by decide +kernel
theorem adj_5_7 : data.adjEnt 5 7 = true := by decide +kernel
theorem adj_5 : data.adjRow 5 = true := data.adjRow_of 5 (by
  intro k hk; simp only [show data.V = 8 from rfl] at hk; interval_cases k
  · exact adj_5_0
  · exact adj_5_1
  · exact adj_5_2
  · exact adj_5_3
  · exact adj_5_4
  · exact adj_5_5
  · exact adj_5_6
  · exact adj_5_7
  )
theorem adj_6_0 : data.adjEnt 6 0 = true := by decide +kernel
theorem adj_6_1 : data.adjEnt 6 1 = true := by decide +kernel
theorem adj_6_2 : data.adjEnt 6 2 = true := by decide +kernel
theorem adj_6_3 : data.adjEnt 6 3 = true := by decide +kernel
theorem adj_6_4 : data.adjEnt 6 4 = true := by decide +kernel
theorem adj_6_5 : data.adjEnt 6 5 = true := by decide +kernel
theorem adj_6_6 : data.adjEnt 6 6 = true := by decide +kernel
theorem adj_6_7 : data.adjEnt 6 7 = true := by decide +kernel
theorem adj_6 : data.adjRow 6 = true := data.adjRow_of 6 (by
  intro k hk; simp only [show data.V = 8 from rfl] at hk; interval_cases k
  · exact adj_6_0
  · exact adj_6_1
  · exact adj_6_2
  · exact adj_6_3
  · exact adj_6_4
  · exact adj_6_5
  · exact adj_6_6
  · exact adj_6_7
  )
theorem adj_7_0 : data.adjEnt 7 0 = true := by decide +kernel
theorem adj_7_1 : data.adjEnt 7 1 = true := by decide +kernel
theorem adj_7_2 : data.adjEnt 7 2 = true := by decide +kernel
theorem adj_7_3 : data.adjEnt 7 3 = true := by decide +kernel
theorem adj_7_4 : data.adjEnt 7 4 = true := by decide +kernel
theorem adj_7_5 : data.adjEnt 7 5 = true := by decide +kernel
theorem adj_7_6 : data.adjEnt 7 6 = true := by decide +kernel
theorem adj_7_7 : data.adjEnt 7 7 = true := by decide +kernel
theorem adj_7 : data.adjRow 7 = true := data.adjRow_of 7 (by
  intro k hk; simp only [show data.V = 8 from rfl] at hk; interval_cases k
  · exact adj_7_0
  · exact adj_7_1
  · exact adj_7_2
  · exact adj_7_3
  · exact adj_7_4
  · exact adj_7_5
  · exact adj_7_6
  · exact adj_7_7
  )
theorem adj_all : ∀ i < data.V, data.adjRow i = true := by
  intro i hi; simp only [show data.V = 8 from rfl] at hi; interval_cases i
  · exact adj_0
  · exact adj_1
  · exact adj_2
  · exact adj_3
  · exact adj_4
  · exact adj_5
  · exact adj_6
  · exact adj_7

theorem curveDeg_ok : data.curveDeg = true := by decide +kernel
def CP (j : ℕ) : Bool := data.curveAt ((j : ℚ) + 2)
theorem cp_0 : CP 0 = true := by decide +kernel
theorem cp_1 : CP 1 = true := by decide +kernel
theorem cp_2 : CP 2 = true := by decide +kernel
theorem cp_3 : CP 3 = true := by decide +kernel
theorem cp_4 : CP 4 = true := by decide +kernel
theorem cp_5 : CP 5 = true := by decide +kernel
theorem cp_6 : CP 6 = true := by decide +kernel
theorem cp_7 : CP 7 = true := by decide +kernel
theorem cp_8 : CP 8 = true := by decide +kernel
theorem cp_all : ∀ j < data.dmaxC + 1, data.curveAt ((j : ℚ) + 2) = true := by
  intro j hj; simp only [show data.dmaxC = 8 from rfl] at hj
  show CP j = true
  interval_cases j
  · exact cp_0
  · exact cp_1
  · exact cp_2
  · exact cp_3
  · exact cp_4
  · exact cp_5
  · exact cp_6
  · exact cp_7
  · exact cp_8

theorem idx_ok : data.idxCheck = true := by decide +kernel
theorem deg_0 : data.degRow 0 = true := by decide +kernel
theorem deg_1 : data.degRow 1 = true := by decide +kernel
theorem deg_2 : data.degRow 2 = true := by decide +kernel
theorem deg_3 : data.degRow 3 = true := by decide +kernel
theorem deg_4 : data.degRow 4 = true := by decide +kernel
theorem deg_5 : data.degRow 5 = true := by decide +kernel
theorem deg_6 : data.degRow 6 = true := by decide +kernel
theorem deg_7 : data.degRow 7 = true := by decide +kernel
theorem deg_all : ∀ i < data.V, data.degRow i = true := by
  intro i hi; simp only [show data.V = 8 from rfl] at hi; interval_cases i
  · exact deg_0
  · exact deg_1
  · exact deg_2
  · exact deg_3
  · exact deg_4
  · exact deg_5
  · exact deg_6
  · exact deg_7

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
theorem pt_15 : PT 15 = true := by decide +kernel
theorem pt_16 : PT 16 = true := by decide +kernel
theorem pt_all : ∀ j < data.dmax + 1, data.pointOK ((j : ℚ) + 2) = true := by
  intro j hj; simp only [show data.dmax = 16 from rfl] at hj
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
  · exact pt_15
  · exact pt_16


/-! ## Satserna

Koefficienterna ligger i `K` = rationella funktioner i parametrarna `a`, `b` över `ℚ(r, s)`,
`r² = -1`, `s² = -2`, med nämnare = produkter av faktorerna i `Dl` (se datafilen). Satserna gäller
för **varje** `a`, `b` i en kropp `F` av karakteristik 0 där ingen faktor i `Dl` är noll, och för
varje val av rötterna `r`, `s`.
-/

variable {F : Type} [Field F] [CharZero F] (a b r s : F)

/-- tolkningen av `K`: värdet i parametrarna `a`, `b` -/
def vK : K → F := FrG.val (PK.val a b r s)

section
variable (hr : r ^ 2 = ((-1 : ℤ) : F)) (hs : s ^ 2 = ((-2 : ℤ) : F))
  (hD : ∀ d ∈ Dl, PK.val a b r s d ≠ 0)
include hr hs hD

theorem sound : Sound (vK a b r s) := FrG.sound (PK.sound a b r s hr hs) hD

/-- **Sats A (adjunkten).** `M(x)·A(x) = D(x)·I` för alla `x₁, x₂ ≠ 0`. -/
theorem adjugate (x1 x2 : F) (h1 : x1 ≠ 0) (h2 : x2 ≠ 0) :
    lapMatK (vK a b r s) data.V data.E x1 x2 * lmatK (vK a b r s) data.V data.A x1 x2 =
      levalK (vK a b r s) data.D x1 x2 • (1 : Matrix (Fin data.V) (Fin data.V) F) :=
  adjugate_gen data (sound a b r s hr hs hD) adj_all x1 x2 h1 h2

/-- **Sats B (kurvan).** `D(x(z)) = 0` för alla `z` utanför punkteringarna. -/
theorem curve (z : F) (hz : ∀ q ∈ qv (vK a b r s) data, z ≠ q) :
    levalK (vK a b r s) data.D (xpar (qv (vK a b r s) data) data.ex1 z)
      (xpar (qv (vK a b r s) data) data.ex2 z) = 0 :=
  curve_gen_pts data (sound a b r s hr hs hD) curveDeg_ok cp_all z hz

/-- **Sats C (partialbråken)** för alla `V²` poster. -/
theorem partial_fractions (k l : Fin data.V) (z : F) (hz : ∀ q ∈ qv (vK a b r s) data, z ≠ q) :
    levalK (vK a b r s) (data.A k l) (xpar (qv (vK a b r s) data) data.ex1 z)
        (xpar (qv (vK a b r s) data) data.ex2 z) * dlogv (qv (vK a b r s) data) data.ev1 z =
      levalK (vK a b r s) (eulK data.DT) (xpar (qv (vK a b r s) data) data.ev1 z)
          (xpar (qv (vK a b r s) data) data.ev2 z) *
        pfval (qv (vK a b r s) data) ((data.pfin k l).map fun t' => (t'.1, t'.2.1, vK a b r s t'.2.2))
          ((data.pinf k l).map fun t' => (t'.1, vK a b r s t'.2)) z :=
  partial_fractions_gen data (sound a b r s hr hs hD) idx_ok deg_all pt_all k l z hz

end

/-- **Rimlighet.** I `a = 2/7`, `b = 3/11` är ingen nämnarfaktor noll, för varje val av rötterna
(t.ex. i ℂ: `r = i`, `s = i√2` när `r² = -1`, `s² = -2`). Hypotesen `hD` ovan är alltså uppfyllbar. -/
theorem dl_check : Dl.all (fun d => normOK (evalZ4 (2 / 7) (3 / 11) d)) = true := by decide +kernel

theorem hD_satisfiable (hr : r ^ 2 = ((-1 : ℤ) : F)) (hs : s ^ 2 = ((-2 : ℤ) : F)) :
    ∀ d ∈ Dl, PK.val (((2 / 7 : ℚ)) : F) (((3 / 11 : ℚ)) : F) r s d ≠ 0 :=
  dl_ne_of_check r s hr hs _ _ Dl dl_check

end Cf2bwK
end LeanResidy.X
