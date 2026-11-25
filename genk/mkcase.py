"""Skriv fallfilen (kärnans räkningar + satserna) för ett Kroneckerpackat datapaket.
python3 mkcase.py NS DATAMODUL V DMAX DMAXC A B UT.lean
"""
import sys
ns, datamod, V, dmax, dmaxC, A, B, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6], sys.argv[7], sys.argv[8]
L = [f"import {datamod}\nimport LeanResidy.X.KronSanity\n",
     "/-!\n# Maskinkontrollerade identiteter, Kroneckerpackade modellen\n\n"
     "Satserna följer ur `adjugate_gen`, `curve_gen_pts` och `partial_fractions_gen` i `X/Case.lean`\n"
     "med koefficientmodellen `K = FrG (PK A B Kb S) Dl` (`X/Kron.lean`, `X/FrG.lean`).\n-/\n",
     "set_option linter.unusedSectionVars false\nset_option Elab.async false\n",
     f"namespace LeanResidy.X\nnamespace {ns}\nopen LeanResidy.Comp\n",
     "/-! ## Kärnans räkningar -/\n"]
for i in range(V):
    for k in range(V):
        L.append(f"theorem adj_{i}_{k} : data.adjEnt {i} {k} = true := by decide +kernel")
    L.append(f"theorem adj_{i} : data.adjRow {i} = true := data.adjRow_of {i} (by\n"
             "  intro k hk; simp only [show data.V = " + str(V) + " from rfl] at hk; interval_cases k\n" +
             "".join(f"  · exact adj_{i}_{k}\n" for k in range(V)) + "  )")
L.append("theorem adj_all : ∀ i < data.V, data.adjRow i = true := by\n"
         "  intro i hi; simp only [show data.V = " + str(V) + " from rfl] at hi; interval_cases i\n" + "".join(f"  · exact adj_{i}\n" for i in range(V)))
L.append("theorem curveDeg_ok : data.curveDeg = true := by decide +kernel")
L.append("def CP (j : ℕ) : Bool := data.curveAt ((j : ℚ) + 2)")
for j in range(dmaxC + 1):
    L.append(f"theorem cp_{j} : CP {j} = true := by decide +kernel")
L.append("theorem cp_all : ∀ j < data.dmaxC + 1, data.curveAt ((j : ℚ) + 2) = true := by\n"
         "  intro j hj; simp only [show data.dmaxC = " + str(dmaxC) + " from rfl] at hj\n  show CP j = true\n  interval_cases j\n" +
         "".join(f"  · exact cp_{j}\n" for j in range(dmaxC + 1)))
L.append("theorem idx_ok : data.idxCheck = true := by decide +kernel")
for i in range(V):
    L.append(f"theorem deg_{i} : data.degRow {i} = true := by decide +kernel")
L.append("theorem deg_all : ∀ i < data.V, data.degRow i = true := by\n"
         "  intro i hi; simp only [show data.V = " + str(V) + " from rfl] at hi; interval_cases i\n" + "".join(f"  · exact deg_{i}\n" for i in range(V)))
L.append("def PT (j : ℕ) : Bool := data.pointOK ((j : ℚ) + 2)")
for j in range(dmax + 1):
    L.append(f"theorem pt_{j} : PT {j} = true := by decide +kernel")
L.append("theorem pt_all : ∀ j < data.dmax + 1, data.pointOK ((j : ℚ) + 2) = true := by\n"
         "  intro j hj; simp only [show data.dmax = " + str(dmax) + " from rfl] at hj\n  show PT j = true\n  interval_cases j\n" +
         "".join(f"  · exact pt_{j}\n" for j in range(dmax + 1)))
L.append(f"""
/-! ## Satserna

Koefficienterna ligger i `K` = rationella funktioner i parametrarna `a`, `b` över `ℚ(r, s)`,
`r² = {A}`, `s² = {B}`, med nämnare = produkter av faktorerna i `Dl` (se datafilen). Satserna gäller
för **varje** `a`, `b` i en kropp `F` av karakteristik 0 där ingen faktor i `Dl` är noll, och för
varje val av rötterna `r`, `s`.
-/

variable {{F : Type}} [Field F] [CharZero F] (a b r s : F)

/-- tolkningen av `K`: värdet i parametrarna `a`, `b` -/
def vK : K → F := FrG.val (PK.val a b r s)

section
variable (hr : r ^ 2 = (({A} : ℤ) : F)) (hs : s ^ 2 = (({B} : ℤ) : F))
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

theorem hD_satisfiable (hr : r ^ 2 = (({A} : ℤ) : F)) (hs : s ^ 2 = (({B} : ℤ) : F)) :
    ∀ d ∈ Dl, PK.val (((2 / 7 : ℚ)) : F) (((3 / 11 : ℚ)) : F) r s d ≠ 0 :=
  dl_ne_of_check r s hr hs _ _ Dl dl_check

end {ns}
end LeanResidy.X
""")
open(out, 'w').write("\n".join(L))
