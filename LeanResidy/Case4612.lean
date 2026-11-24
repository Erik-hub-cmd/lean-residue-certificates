import LeanResidy.Points
import LeanResidy.Data4612

/-!
# 4.6.12 med vikt 1/5 (artikel 2): maskinkontrollerade identiteter

Kropp `K = ℚ(r, s)`, `r² = KA`, `s² = KB` (se datafilen). Satserna gäller för **varje** val av kvadratrötter
`r`, `s` i en kropp `F` av karakteristik 0 (t.ex. ℂ), alltså både för parametriseringen `P` och för
dess Galoiskonjugat `Pτ`.

* `adjugate`: `M(x)·A(x) = D(x)·I` (laplacianen, den explicita adjunkten `A` och determinanten `D`).
* `curve`: `D(x(z)) = 0` för alla `z` utanför punkteringarna.
* `partial_fractions`: för alla 144 poster `(k, l)`:
  `A_{kl}(x(z))·(v₁'/v₁)(z) = (v₂∂_{v₂}D^T)(v(z))·PF_{kl}(z)`.
-/

set_option linter.unusedSectionVars false
-- sekventiellt: varje kärnkörning behöver flera GB minne
set_option Elab.async false

namespace LeanResidy
namespace C4612
open LeanResidy.Comp

/-- `D^T`: determinanten i koordinaterna `v = x^{T⁻¹}` -/
def DT : LP := trL t00 t01 t10 t11 D
def pfin (k l : ℕ) : List (ℕ × ℕ × K) := PFfinL.getD (k * V + l) []
def pinf (k l : ℕ) : List (ℕ × K) := PFinfL.getD (k * V + l) []
/-- index för punkten 0 i `pts` -/
def iz : ℕ := pts.length - 1

/-! ## Kontrollfunktioner (räknas av kärnan) -/

abbrev Z := Fr K pts
def X1 : Z := frPar pts ex1
def X1i : Z := frPar pts (ex1.map (- ·))
def X2 : Z := frPar pts ex2
def X2i : Z := frPar pts (ex2.map (- ·))


abbrev MK := List (Mon K)

/-- post `(k, l)` av identiteten, som monomsumma (bara exponenterna används av kärnan) -/
def entryS (k l : ℕ) : MK :=
  smul (slev (A k l) (spar ex1) (spar (ex1.map (- ·))) (spar ex2) (spar (ex2.map (- ·))))
      (sdlog ev1) ++
    sneg (smul (slev (eul DT) (spar ev1) (spar (ev1.map (- ·))) (spar ev2) (spar (ev2.map (- ·))))
      (spf iz (pfin k l) (pinf k l)))

/-- gradgräns -/
def dmax : ℕ := 34

def degCheck : Bool :=
  (List.range V).all fun k => (List.range V).all fun l =>
    (entryS k l).all (fun m => leN pts.length m.2 (kvecs (entryS k l))) &&
      decide (sdeg pts.length (entryS k l) (kvecs (entryS k l)) ≤ dmax)

def pointOK (c : ℚ) : Bool :=
  okAt pts c &&
  (let ws := wsAt pts c
   let wis := ws.map Z4.inv
   let x1 := pvP ws wis ex1
   let x1i := pvP ws wis (ex1.map (- ·))
   let x2 := pvP ws wis ex2
   let x2i := pvP ws wis (ex2.map (- ·))
   let v1 := pvP ws wis ev1
   let v1i := pvP ws wis (ev1.map (- ·))
   let v2 := pvP ws wis ev2
   let v2i := pvP ws wis (ev2.map (- ·))
   let dl := dlogP ev1 wis
   let ed := lev (eul DT) v1 v1i v2 v2i
   (List.range V).all fun k => (List.range V).all fun l =>
     Comp.isZero (Comp.add (Comp.mul (lev (A k l) x1 x1i x2 x2i) dl)
       (Comp.neg (Comp.mul ed (pfP c (pfin k l) (pinf k l) wis)))))

def idxCheck : Bool :=
  PFfinL.all (fun f => f.all fun t => decide (t.1 < pts.length)) &&
    decide (ev1.length ≤ pts.length) && decide (iz < pts.length) &&
    decide (pts.getD iz Comp.zero = ⟨0, 0, 0, 0⟩)

/-! ## Kärnans räkningar -/

/-- en post av adjunktkontrollen (samma uttryck som i `adjCheck`) -/
def adjEntry (i k : ℕ) : Bool :=
  Comp.isZero (Comp.add (sumC ((List.range V).map fun j =>
      (Comp.mul (bev (lapL E i j)) (bev (A j k)) : Q3)))
    (Comp.neg (if i = k then bev D else Comp.zero)))

def adjRow (i : ℕ) : Bool := (List.range V).all fun k => adjEntry i k

-- 4.6.12 är för stort för en enda kärnkörning (minnet): en sats per rad och en per punkt.
theorem adjRow_0 : adjRow 0 = true := by decide +kernel
theorem adjRow_1 : adjRow 1 = true := by decide +kernel
theorem adjRow_2 : adjRow 2 = true := by decide +kernel
theorem adjRow_3 : adjRow 3 = true := by decide +kernel
theorem adjRow_4 : adjRow 4 = true := by decide +kernel
theorem adjRow_5 : adjRow 5 = true := by decide +kernel
theorem adjRow_6 : adjRow 6 = true := by decide +kernel
theorem adjRow_7 : adjRow 7 = true := by decide +kernel
theorem adjRow_8 : adjRow 8 = true := by decide +kernel
theorem adjRow_9 : adjRow 9 = true := by decide +kernel
theorem adjRow_10 : adjRow 10 = true := by decide +kernel
theorem adjRow_11 : adjRow 11 = true := by decide +kernel

theorem adjCheck_ok : adjCheck V E A D = true := by
  have hrows : ∀ i < 12, adjRow i = true := by
    intro i hi
    interval_cases i
    exacts [adjRow_0, adjRow_1, adjRow_2, adjRow_3, adjRow_4, adjRow_5, adjRow_6, adjRow_7, adjRow_8, adjRow_9, adjRow_10, adjRow_11]
  unfold adjCheck
  rw [List.all_eq_true]
  intro i hi
  exact hrows i (List.mem_range.mp hi)
/-! Kurvan med punktmetoden (Fr-räkningen tar för mycket minne för 4.6.12). -/
def curveS : MK := slev D (spar ex1) (spar (ex1.map (- ·))) (spar ex2) (spar (ex2.map (- ·)))
def dcurve : ℕ := 24
def curveDeg : Bool :=
  curveS.all (fun m => leN pts.length m.2 (kvecs curveS)) &&
    decide (sdeg pts.length curveS (kvecs curveS) ≤ dcurve)
def curvePt (c : ℚ) : Bool :=
  okAt pts c &&
  (let ws := wsAt pts c
   let wis := ws.map Z4.inv
   Comp.isZero (lev D (pvP ws wis ex1) (pvP ws wis (ex1.map (- ·))) (pvP ws wis ex2)
     (pvP ws wis (ex2.map (- ·)))))
theorem curveDeg_ok : curveDeg = true := by decide +kernel
theorem curvePts_a : ((List.range 13).all fun j => curvePt ((j : ℚ) + 2)) = true := by
  decide +kernel
theorem curvePts_b : ((List.range 12).all fun j => curvePt ((j : ℚ) + 15)) = true := by
  decide +kernel
theorem curvePts_ok : ((List.range (dcurve + 1)).all fun j => curvePt ((j : ℚ) + 2)) = true := by
  have ha := curvePts_a; have hb := curvePts_b
  simp only [List.all_eq_true, List.mem_range] at ha hb ⊢
  intro j hj
  rcases Nat.lt_or_ge j 13 with h | h
  · exact ha j h
  · have := hb (j - 13) (by simp [dcurve] at hj; omega)
    rwa [show ((j - 13 : ℕ) : ℚ) + 15 = (j : ℚ) + 2 by push_cast [Nat.cast_sub h]; ring] at this
theorem idxCheck_ok : idxCheck = true := by decide +kernel
def degRow (k : ℕ) : Bool := (List.range V).all fun l =>
    (entryS k l).all (fun m => leN pts.length m.2 (kvecs (entryS k l))) &&
      decide (sdeg pts.length (entryS k l) (kvecs (entryS k l)) ≤ dmax)
theorem degRow_0 : degRow 0 = true := by decide +kernel
theorem degRow_1 : degRow 1 = true := by decide +kernel
theorem degRow_2 : degRow 2 = true := by decide +kernel
theorem degRow_3 : degRow 3 = true := by decide +kernel
theorem degRow_4 : degRow 4 = true := by decide +kernel
theorem degRow_5 : degRow 5 = true := by decide +kernel
theorem degRow_6 : degRow 6 = true := by decide +kernel
theorem degRow_7 : degRow 7 = true := by decide +kernel
theorem degRow_8 : degRow 8 = true := by decide +kernel
theorem degRow_9 : degRow 9 = true := by decide +kernel
theorem degRow_10 : degRow 10 = true := by decide +kernel
theorem degRow_11 : degRow 11 = true := by decide +kernel

theorem degCheck_ok : degCheck = true := by
  have hrows : ∀ i < 12, degRow i = true := by
    intro i hi
    interval_cases i
    exacts [degRow_0, degRow_1, degRow_2, degRow_3, degRow_4, degRow_5, degRow_6, degRow_7, degRow_8, degRow_9, degRow_10, degRow_11]
  unfold degCheck
  rw [List.all_eq_true]
  intro i hi
  exact hrows i (List.mem_range.mp hi)
theorem point_0 : pointOK (((0 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_1 : pointOK (((1 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_2 : pointOK (((2 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_3 : pointOK (((3 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_4 : pointOK (((4 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_5 : pointOK (((5 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_6 : pointOK (((6 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_7 : pointOK (((7 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_8 : pointOK (((8 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_9 : pointOK (((9 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_10 : pointOK (((10 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_11 : pointOK (((11 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_12 : pointOK (((12 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_13 : pointOK (((13 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_14 : pointOK (((14 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_15 : pointOK (((15 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_16 : pointOK (((16 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_17 : pointOK (((17 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_18 : pointOK (((18 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_19 : pointOK (((19 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_20 : pointOK (((20 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_21 : pointOK (((21 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_22 : pointOK (((22 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_23 : pointOK (((23 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_24 : pointOK (((24 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_25 : pointOK (((25 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_26 : pointOK (((26 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_27 : pointOK (((27 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_28 : pointOK (((28 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_29 : pointOK (((29 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_30 : pointOK (((30 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_31 : pointOK (((31 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_32 : pointOK (((32 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_33 : pointOK (((33 : ℕ) : ℚ) + 2) = true := by decide +kernel
theorem point_34 : pointOK (((34 : ℕ) : ℚ) + 2) = true := by decide +kernel

theorem points_ok (j : ℕ) (hj : j < dmax + 1) : pointOK ((j : ℚ) + 2) = true := by
  have hj' : j < 35 := hj
  interval_cases j
  exacts [point_0, point_1, point_2, point_3, point_4, point_5, point_6, point_7, point_8, point_9, point_10, point_11, point_12, point_13, point_14, point_15, point_16, point_17, point_18, point_19, point_20, point_21, point_22, point_23, point_24, point_25, point_26, point_27, point_28, point_29, point_30, point_31, point_32, point_33, point_34]

/-! ## Satserna -/

variable {F : Type} [Field F] [CharZero F]

/-- punkteringarna i `F` (den sista är 0) -/
def qv (r s : F) : List F := pts.map (Z4.val r s)

/-- **Sats A (adjunkten).** `M(x)·A(x) = D(x)·I` för alla `x₁, x₂ ≠ 0`, där `M` är laplacianen för
4.6.12 med vikt 1/5 (artikel 2) och `A`, `D` de explicita Laurentpolynomen. Alltså `G(x) = A(x)/D(x)` där `D ≠ 0`. -/
theorem adjugate (x1 x2 : F) (h1 : x1 ≠ 0) (h2 : x2 ≠ 0) :
    lapMat V E x1 x2 * lmat V A x1 x2 = leval D x1 x2 • (1 : Matrix (Fin V) (Fin V) F) :=
  adj_of_check V E A D adjCheck_ok x1 x2 h1 h2

section
variable (r s : F) (hr : r ^ 2 = KA) (hs : s ^ 2 = KB)
include hr hs

private theorem hz' (z : F) (hz : ∀ q ∈ qv r s, z ≠ q) : ∀ q ∈ pts, z ≠ Z4.val r s q :=
  fun q hq => hz _ (List.mem_map_of_mem hq)

/-- **Sats B (kurvan).** `D(x(z)) = 0` för alla `z` utanför punkteringarna. -/
theorem curve (z : F) (hz : ∀ q ∈ qv r s, z ≠ q) :
    leval D (xpar (qv r s) ex1 z) (xpar (qv r s) ex2 z) = 0 := by
  have S4 := Z4.sound r s hr hs
  have hsv : ∀ w : F, (∀ q ∈ qv r s, w ≠ q) →
      sval (Z4.val r s) (qv r s) w curveS = leval D (xpar (qv r s) ex1 w) (xpar (qv r s) ex2 w) := by
    intro w hw
    simp only [curveS]
    rw [sval_lev S4 _ w hw _ _ _ _ _ (by rw [sval_par_inv S4 _ w hw, sval_par S4 _ w hw])
      (by rw [sval_par_inv S4 _ w hw, sval_par S4 _ w hw]), sval_par S4 _ w hw, sval_par S4 _ w hw]
  have hdeg := curveDeg_ok
  simp only [curveDeg, Bool.and_eq_true, decide_eq_true_eq] at hdeg
  have hpts := curvePts_ok
  simp only [List.all_eq_true, List.mem_range] at hpts
  have hv := vanish (v := Z4.val r s) (qv r s) curveS (kvecs curveS) dcurve
    (by simpa [qv] using hdeg.1) (by simpa [qv] using hdeg.2)
    (fun j hj => by
      have h := hpts j hj
      simp only [curvePt, Bool.and_eq_true] at h
      obtain ⟨hok, h⟩ := h
      have hzc : ∀ q ∈ qv r s, (((j : ℚ) + 2 : ℚ) : F) ≠ q := okAt_nonpunct r s hr hs pts _ hok
      have hzc' : ∀ q ∈ qv r s, ((j : F) + 2) ≠ q := by simpa using hzc
      refine ⟨hzc', ?_⟩
      rw [hsv _ hzc']
      have h := S4.isZero _ h
      have hw := okAt_hw r s hr hs pts ((j : ℚ) + 2)
      have hwi := okAt_hwi r s hr hs pts ((j : ℚ) + 2) hok
      have hl1 : (wsAt pts ((j : ℚ) + 2)).length = (qv r s).length := by simp [wsAt, qv]
      have hl2 : ((wsAt pts ((j : ℚ) + 2)).map Z4.inv).length = (qv r s).length := by
        simp [wsAt, qv]
      have P := fun es => val_pvP S4 (qv r s) (((j : ℚ) + 2 : ℚ) : F) (wsAt pts ((j : ℚ) + 2))
        ((wsAt pts ((j : ℚ) + 2)).map Z4.inv) hl1 hl2 hw hwi es
      rw [val_lev S4 _ _ _ _ _ (by rw [P, P, pe_neg _ _ hzc]) (by rw [P, P, pe_neg _ _ hzc]),
        P, P] at h
      simpa [xpar_eq_pe] using h) z hz
  rw [hsv z hz] at hv
  exact hv

/-- uttrycket i Sats C, `vänsterled − högerled` -/
def entryE (k l : ℕ) (z : F) : F :=
  leval (A k l) (xpar (qv r s) ex1 z) (xpar (qv r s) ex2 z) * dlogv (qv r s) ev1 z -
    leval (eul DT) (xpar (qv r s) ev1 z) (xpar (qv r s) ev2 z) *
      pfval (qv r s) ((pfin k l).map fun t => (t.1, t.2.1, Z4.val r s t.2.2))
        ((pinf k l).map fun t => (t.1, Z4.val r s t.2)) z

omit hr hs in
private theorem pfin_idx (k l : ℕ) (hidx : idxCheck = true) :
    (pfin k l).all (fun t => decide (t.1 < (qv r s).length)) = true := by
  simp only [idxCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hidx
  simp only [pfin, qv, List.length_map, List.all_eq_true, decide_eq_true_eq]
  rw [List.getD_eq_getElem?_getD]
  rcases hget : PFfinL[k * V + l]? with _ | f
  · simp
  · simpa using hidx.1.1.1 f (List.mem_of_getElem? hget)

private theorem idx_facts : ev1.length ≤ (qv r s).length ∧ iz < (qv r s).length ∧
    (qv r s).getD iz 0 = 0 := by
  have h := idxCheck_ok
  simp only [idxCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨by simpa [qv] using h.1.1.2, by simpa [qv] using h.1.2, ?_⟩
  have hl : iz < pts.length := h.1.2
  rw [qv, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl,
    Option.map_some, Option.getD_some]
  have h2 := h.2
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some] at h2
  rw [h2]; simp [Z4.val]

/-- monomsumman har värdet `entryE` -/
private theorem sval_entry (k l : ℕ) (z : F) (hz : ∀ q ∈ qv r s, z ≠ q) :
    sval (Z4.val r s) (qv r s) z (entryS k l) = entryE r s k l z := by
  have S4 := Z4.sound r s hr hs
  obtain ⟨hl, hiz, h0⟩ := idx_facts r s hr hs
  simp only [entryS, entryE]
  rw [sval_append S4 _ z, sval_neg S4 _ z, sval_mul S4 _ z hz, sval_mul S4 _ z hz,
    sval_lev S4 _ z hz _ _ _ _ _ (by rw [sval_par_inv S4 _ z hz, sval_par S4 _ z hz])
      (by rw [sval_par_inv S4 _ z hz, sval_par S4 _ z hz]),
    sval_lev S4 _ z hz _ _ _ _ _ (by rw [sval_par_inv S4 _ z hz, sval_par S4 _ z hz])
      (by rw [sval_par_inv S4 _ z hz, sval_par S4 _ z hz]),
    sval_par S4 _ z hz, sval_par S4 _ z hz, sval_par S4 _ z hz, sval_par S4 _ z hz,
    sval_dlog S4 _ z hz _ hl, sval_pf S4 _ z hz _ hiz h0 _ _ (pfin_idx r s k l idxCheck_ok)]
  ring

/-- i en kontrollpunkt är `entryE` noll (exakt aritmetik i ℚ(r, s)) -/
private theorem point_entry (c : ℚ) (h : pointOK c = true) (k l : ℕ) (hk : k < V) (hl : l < V) :
    entryE r s k l (c : F) = 0 := by
  have S4 := Z4.sound r s hr hs
  obtain ⟨hlen, hiz, h0⟩ := idx_facts r s hr hs
  simp only [pointOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨hok, h⟩ := h
  have h := S4.isZero _ (h k hk l hl)
  have hw := okAt_hw r s hr hs pts c
  have hwi := okAt_hwi r s hr hs pts c hok
  have hzc : ∀ q ∈ qv r s, (c : F) ≠ q := okAt_nonpunct r s hr hs pts c hok
  have hl1 : (wsAt pts c).length = (qv r s).length := by simp [wsAt, qv]
  have hl2 : ((wsAt pts c).map Z4.inv).length = (qv r s).length := by simp [wsAt, qv]
  have P := fun es => val_pvP S4 (qv r s) (c : F) (wsAt pts c) ((wsAt pts c).map Z4.inv) hl1 hl2
    hw hwi es
  rw [S4.add, S4.neg, S4.mul, S4.mul,
    val_lev S4 _ _ _ _ _ (by rw [P, P, pe_neg _ _ hzc]) (by rw [P, P, pe_neg _ _ hzc]),
    val_lev S4 _ _ _ _ _ (by rw [P, P, pe_neg _ _ hzc]) (by rw [P, P, pe_neg _ _ hzc]),
    P, P, P, P, val_dlogP S4 (qv r s) (c : F) _ hwi _ hlen,
    val_pfP S4 (qv r s) c _ hwi _ _ (pfin_idx r s k l idxCheck_ok)] at h
  simp only [entryE, xpar_eq_pe]
  linear_combination h

/-- **Sats C (partialbråken).** För varje post `(k, l)` och varje `z` utanför punkteringarna:
`A_{kl}(x(z)) · (v₁'/v₁)(z) = (v₂ ∂_{v₂} D^T)(v(z)) · PF_{kl}(z)`,
där `v = x^{T⁻¹}` (`T` i datafilen), `v₁'/v₁ = Σ eᵢ/(z − qᵢ)` och `PF_{kl}` är det explicita
partialbråket med poler bara i punkteringarna och 0 (plus en polynomdel = polen i ∞). Integranden
`ρ_{kl} = A_{kl}·(v₁'/v₁)/(v₂∂_{v₂}D^T)` är alltså exakt `PF_{kl}`: inga andra poler, och
residyerna är koefficienterna med `m = 1`. -/
theorem partial_fractions (k l : Fin V) (z : F) (hz : ∀ q ∈ qv r s, z ≠ q) :
    leval (A k l) (xpar (qv r s) ex1 z) (xpar (qv r s) ex2 z) * dlogv (qv r s) ev1 z =
      leval (eul DT) (xpar (qv r s) ev1 z) (xpar (qv r s) ev2 z) *
        pfval (qv r s) ((pfin k l).map fun t => (t.1, t.2.1, Z4.val r s t.2.2))
          ((pinf k l).map fun t => (t.1, Z4.val r s t.2)) z := by
  have S4 := Z4.sound r s hr hs
  have hdeg := degCheck_ok
  simp only [degCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hdeg
  obtain ⟨hle, hd⟩ := hdeg k k.2 l l.2
  have hv := vanish (v := Z4.val r s) (qv r s) (entryS k l) (kvecs (entryS k l)) dmax
    (by simpa [qv] using hle) (by simpa [qv] using hd)
    (fun j hj => ⟨by
        have := okAt_nonpunct r s hr hs pts ((j : ℚ) + 2) (by
          have := points_ok j hj; simp only [pointOK, Bool.and_eq_true] at this; exact this.1)
        simpa [qv] using this,
      by rw [sval_entry r s hr hs k l _ (by
            have := okAt_nonpunct r s hr hs pts ((j : ℚ) + 2) (by
              have := points_ok j hj; simp only [pointOK, Bool.and_eq_true] at this; exact this.1)
            simpa [qv] using this)]
         have := point_entry r s hr hs ((j : ℚ) + 2) (points_ok j hj) k l k.2 l.2
         simpa using this⟩) z hz
  rw [sval_entry r s hr hs k l z hz, entryE] at hv
  linear_combination hv

end

end C4612
end LeanResidy
