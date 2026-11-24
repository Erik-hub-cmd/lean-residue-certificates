"""Skriver LeanResidy/X/Case<namn>.lean: kärnans räkningar och satserna för ett fall.
Kör: python3 make_x.py <namn> <dmax> '<titel>' <valtyp>   valtyp: z8 | z4 | (andra: se filen)"""
import sys, os
name, dmax, title, kind = sys.argv[1], int(sys.argv[2]), sys.argv[3], sys.argv[4]
V = int(sys.argv[5])
ns = 'C' + name
p = os.path.expanduser(f'~/lr/LeanResidy/X/Data{name}.lean')
import re
s = re.sub(r'dmax := (DMAX|\d+)', f'dmax := {dmax}', open(p).read())
CPTS = int(os.environ.get('CURVEPTS', '-1'))
if CPTS >= 0:
    s = re.sub(r'\n  dmaxC := \d+', '', s)
    s = s.replace(f'dmax := {dmax}', f'dmax := {dmax}\n  dmaxC := {CPTS}')
open(p, 'w').write(s)
L = [f"import LeanResidy.X.Data{name}\n",
     f"/-!\n# {title}: maskinkontrollerade identiteter (generiska ramverket `LeanResidy.X`)\n\n"
     "Datat finns i `Data" + name + ".lean`; satserna följer ur `adjugate_gen`, `curve_gen` och\n"
     "`partial_fractions_gen` i `X/Case.lean` sedan kärnan räknat ut kontrollerna nedan.\n-/\n",
     "set_option linter.unusedSectionVars false\n",
     "namespace LeanResidy.X", f"namespace {ns}", "open LeanResidy.Comp\n",
     "/-! ## Kärnans räkningar -/\n"]
L.insert(3, "set_option Elab.async false\n")
for i in range(V):
    for k in range(V):
        L.append(f"theorem adj_{i}_{k} : data.adjEnt {i} {k} = true := by decide +kernel")
    L.append(f"theorem adj_{i} : data.adjRow {i} = true := data.adjRow_of {i} (by\n  intro k hk; simp only [data] at hk; interval_cases k\n" + "".join(f"  · exact adj_{i}_{k}\n" for k in range(V)) + "  )")
if CPTS < 0:
    L.append("theorem curve_ok : data.curveCheck = true := by decide +kernel")
else:
    L.append("theorem curveDeg_ok : data.curveDeg = true := by decide +kernel")
    L.append("def CP (j : ℕ) : Bool := data.curveAt ((j : ℚ) + 2)")
    for j in range(CPTS + 1):
        L.append(f"theorem cp_{j} : CP {j} = true := by decide +kernel")
    L.append("theorem cp_all : ∀ j < data.dmaxC + 1, data.curveAt ((j : ℚ) + 2) = true := by\n"
             "  intro j hj; simp only [data] at hj\n  show CP j = true\n  interval_cases j\n" +
             "".join(f"  · exact cp_{j}\n" for j in range(CPTS + 1)))
L.append("theorem idx_ok : data.idxCheck = true := by decide +kernel")
for i in range(V):
    L.append(f"theorem deg_{i} : data.degRow {i} = true := by decide +kernel")
L.append("\ndef PT (j : ℕ) : Bool := data.pointOK ((j : ℚ) + 2)")
for j in range(dmax + 1):
    L.append(f"theorem pt_{j} : PT {j} = true := by decide +kernel")
L.append("\ntheorem adj_all : ∀ i < data.V, data.adjRow i = true := by\n"
         "  intro i hi; simp only [data] at hi; interval_cases i\n" +
         "".join(f"  · exact adj_{i}\n" for i in range(V)))
L.append("theorem deg_all : ∀ i < data.V, data.degRow i = true := by\n"
         "  intro i hi; simp only [data] at hi; interval_cases i\n" +
         "".join(f"  · exact deg_{i}\n" for i in range(V)))
L.append("theorem pt_all : ∀ j < data.dmax + 1, data.pointOK ((j : ℚ) + 2) = true := by\n"
         "  intro j hj; simp only [data] at hj\n  show PT j = true\n  interval_cases j\n" +
         "".join(f"  · exact pt_{j}\n" for j in range(dmax + 1)))
A_, B_ = sys.argv[6], sys.argv[7]
if kind == 'fr1':
    L.append(f"""/-! ## Satserna

Koefficienterna ligger i `K` = rationella funktioner i parametern `u` (se datafilen) över `ℚ(r, s)`,
`r² = {A_}`, `s² = {B_}`. Satserna gäller för **varje** `u` i en kropp `F` av karakteristik 0 utanför de
ändligt många punkterna `tpts` (nämnarnas nollställen och, för kontrollpunkterna, de `u` där en
kontrollpunkt z = 2, 3, … skulle vara en punktering), och för varje val av rötterna `r`, `s`.
-/

variable {{F : Type}} [Field F] [CharZero F] (r s u : F)

/-- tolkningen av `K`: värdet i parametern `u` -/
def vK : K → F := Fr.val (Z4.val r s) u

section
variable (hr : r ^ 2 = (({A_} : ℤ) : F)) (hs : s ^ 2 = (({B_} : ℤ) : F))
  (hu : ∀ p ∈ tpts, u ≠ Z4.val r s p)
include hr hs hu

theorem sound : Sound (vK r s u) := Fr.sound (Z4.sound r s hr hs) u hu
""")
    vargs = "r s u"; sargs = "r s u hr hs hu"
if kind == 'z8':
    L.append("""/-! ## Satserna

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
""")
    vargs = "r s t"; sargs = "r s t hr hs ht"
L.append(("""
/-- **Sats A (adjunkten).** `M(x)·A(x) = D(x)·I` för alla `x₁, x₂ ≠ 0`. -/
theorem adjugate (x1 x2 : F) (h1 : x1 ≠ 0) (h2 : x2 ≠ 0) :
    lapMatK (vK r s t) data.V data.E x1 x2 * lmatK (vK r s t) data.V data.A x1 x2 =
      levalK (vK r s t) data.D x1 x2 • (1 : Matrix (Fin data.V) (Fin data.V) F) :=
  adjugate_gen data (sound r s t hr hs ht) adj_all x1 x2 h1 h2

/-- **Sats B (kurvan).** `D(x(z)) = 0` för alla `z` utanför punkteringarna. -/
theorem curve (z : F) (hz : ∀ q ∈ qv (vK r s t) data, z ≠ q) :
    levalK (vK r s t) data.D (xpar (qv (vK r s t) data) data.ex1 z)
      (xpar (qv (vK r s t) data) data.ex2 z) = 0 :=
  CURVEPROOF

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
""").replace("sound r s t hr hs ht", "sound " + sargs).replace("vK r s t", "vK " + vargs))
L[-1] = L[-1].replace("CURVEPROOF", "curve_gen data (sound r s t hr hs ht) curve_ok z hz" if CPTS < 0 else
                      "curve_gen_pts data (sound r s t hr hs ht) curveDeg_ok cp_all z hz").replace("sound r s t hr hs ht", "sound " + sargs)
L.append(f"end {ns}\nend LeanResidy.X\n")
open(os.path.expanduser(f'~/lr/LeanResidy/X/Case{name}.lean'), 'w').write("\n".join(L))
