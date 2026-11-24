import LeanResidy.X.Generic

/-!
# Ett fall som data, och de tre satserna bevisade en gång för alla fall

`Case K` samlar datat för ett gitter (laplacianen, adjunkten, determinanten, parametriseringen,
koordinatbytet `T` och partialbråken). Kontrollerna (`adjRowK`, `curveCheckK`, `idxCheck`, `degCheck`,
`pointOK`) är booleska funktioner som kärnan räknar ut i fallfilerna; satserna `adjugate_gen`,
`curve_gen` och `partial_fractions_gen` översätter dem till identiteter i en godtycklig kropp `F` av
karakteristik 0 för en godtycklig sund tolkning `vK : K → F`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace LeanResidy
namespace X
open LeanResidy.Comp

structure Case (K : Type) where
  V : ℕ
  E : List (EdgeK K)
  AL : List (LPK K)
  D : LPK K
  /-- punkteringarna; den sista är 0 -/
  pts : List K
  ex1 : List ℤ
  ex2 : List ℤ
  t00 : ℤ
  t01 : ℤ
  t10 : ℤ
  t11 : ℤ
  ev1 : List ℤ
  ev2 : List ℤ
  PFfinL : List (List (ℕ × ℕ × K))
  PFinfL : List (List (ℕ × K))
  dmax : ℕ
  /-- gradgräns för kurvkontrollen med punktmetoden (används bara av `curve_gen_pts`) -/
  dmaxC : ℕ := 0

namespace Case
variable {K : Type} [Comp K] (c : Case K)

def A (i j : ℕ) : LPK K := c.AL.getD (i * c.V + j) []
/-- `D^T`: determinanten i koordinaterna `v = x^{T⁻¹}` -/
def DT : LPK K := trLK c.t00 c.t01 c.t10 c.t11 c.D
def pfin (k l : ℕ) : List (ℕ × ℕ × K) := c.PFfinL.getD (k * c.V + l) []
def pinf (k l : ℕ) : List (ℕ × K) := c.PFinfL.getD (k * c.V + l) []
/-- index för punkten 0 -/
def iz : ℕ := c.pts.length - 1

/-! ## Kontrollerna -/

def adjRow (i : ℕ) : Bool := adjRowK c.V c.E c.A c.D i
def adjEnt (i k : ℕ) : Bool := adjEntK c.V c.E c.A c.D i k

def curveCheck : Bool := curveCheckK c.D c.pts c.ex1 c.ex2

/-- post `(k, l)` av identiteten i Sats C som monomsumma -/
def entryS (k l : ℕ) : List (Mon K) :=
  smul (slevK (c.A k l) (spar c.ex1) (spar (c.ex1.map (- ·))) (spar c.ex2) (spar (c.ex2.map (- ·))))
      (sdlog c.ev1) ++
    sneg (smul (slevK (eulK c.DT) (spar c.ev1) (spar (c.ev1.map (- ·))) (spar c.ev2)
      (spar (c.ev2.map (- ·)))) (spf c.iz (c.pfin k l) (c.pinf k l)))

def degOK (k l : ℕ) : Bool :=
  (c.entryS k l).all (fun m => leN c.pts.length m.2 (kvecs (c.entryS k l))) &&
    decide (sdeg c.pts.length (c.entryS k l) (kvecs (c.entryS k l)) ≤ c.dmax)

def degRow (k : ℕ) : Bool := (List.range c.V).all fun l => c.degOK k l

theorem adjRow_of (i : ℕ) (h : ∀ k < c.V, c.adjEnt i k = true) : c.adjRow i = true := by
  simp only [adjRow, adjRowK, List.all_eq_true, List.mem_range]; exact fun k hk => h k hk

def idxCheck : Bool :=
  c.PFfinL.all (fun f => f.all fun t => decide (t.1 < c.pts.length)) &&
    decide (c.ev1.length ≤ c.pts.length) && decide (c.iz < c.pts.length) &&
    Comp.isZero (c.pts.getD c.iz Comp.zero)

def wsAt (q : ℚ) : List K := c.pts.map fun p => Comp.add (Comp.ofQ q) (Comp.neg p)

variable [CInv K]

def okAt (q : ℚ) : Bool := (c.wsAt q).all fun w => invOK w (CInv.inv w)

/-- post `(k, l)` i punkten `z = q`, exakt i `K` -/
def entryAt (q : ℚ) (k l : ℕ) : Bool :=
  let ws := c.wsAt q
  let wis := ws.map CInv.inv
  let x1 := pvP ws wis c.ex1
  let x1i := pvP ws wis (c.ex1.map (- ·))
  let x2 := pvP ws wis c.ex2
  let x2i := pvP ws wis (c.ex2.map (- ·))
  let v1 := pvP ws wis c.ev1
  let v1i := pvP ws wis (c.ev1.map (- ·))
  let v2 := pvP ws wis c.ev2
  let v2i := pvP ws wis (c.ev2.map (- ·))
  Comp.isZero (Comp.add (Comp.mul (levK id (c.A k l) x1 x1i x2 x2i) (dlogP c.ev1 wis))
    (Comp.neg (Comp.mul (levK id (eulK c.DT) v1 v1i v2 v2i) (pfP q (c.pfin k l) (c.pinf k l) wis))))

def pointOK (q : ℚ) : Bool :=
  c.okAt q && (List.range c.V).all fun k => (List.range c.V).all fun l => c.entryAt q k l

theorem pointOK_of (q : ℚ) (h0 : c.okAt q = true)
    (h : ∀ k < c.V, ∀ l < c.V, c.entryAt q k l = true) : c.pointOK q = true := by
  simp only [pointOK, h0, Bool.true_and, List.all_eq_true, List.mem_range]; exact h

/-! ### Kurvan med punktmetoden (för fall där den exakta räkningen är för stor) -/

def curveS : List (Mon K) :=
  slevK c.D (spar c.ex1) (spar (c.ex1.map (- ·))) (spar c.ex2) (spar (c.ex2.map (- ·)))

def curveDeg : Bool :=
  c.curveS.all (fun m => leN c.pts.length m.2 (kvecs c.curveS)) &&
    decide (sdeg c.pts.length c.curveS (kvecs c.curveS) ≤ c.dmaxC)

def curveAt (q : ℚ) : Bool :=
  c.okAt q &&
  (let ws := c.wsAt q
   let wis := ws.map CInv.inv
   Comp.isZero (levK id c.D (pvP ws wis c.ex1) (pvP ws wis (c.ex1.map (- ·)))
     (pvP ws wis c.ex2) (pvP ws wis (c.ex2.map (- ·)))))

end Case

/-! ## Satserna -/

section Thms
variable {K : Type} [Comp K] {F : Type} [Field F] [CharZero F] (c : Case K) {vK : K → F}
  (S : Sound vK)

/-- punkteringarna i `F` -/
def qv (vK : K → F) (c : Case K) : List F := c.pts.map vK

include S

/-- **Sats A (adjunkten).** -/
theorem adjugate_gen (h : ∀ i < c.V, c.adjRow i = true) (x1 x2 : F) (h1 : x1 ≠ 0) (h2 : x2 ≠ 0) :
    lapMatK vK c.V c.E x1 x2 * lmatK vK c.V c.A x1 x2 =
      levalK vK c.D x1 x2 • (1 : Matrix (Fin c.V) (Fin c.V) F) :=
  adj_of_checkK S c.V c.E c.A c.D h x1 x2 h1 h2

/-- **Sats B (kurvan).** -/
theorem curve_gen (h : c.curveCheck = true) (z : F) (hz : ∀ q ∈ qv vK c, z ≠ q) :
    levalK vK c.D (xpar (qv vK c) c.ex1 z) (xpar (qv vK c) c.ex2 z) = 0 :=
  curve_of_checkK S c.D c.pts c.ex1 c.ex2 h z hz

/-- uttrycket i Sats C, `vänsterled − högerled` -/
def entryE (vK : K → F) (k l : ℕ) (z : F) : F :=
  levalK vK (c.A k l) (xpar (qv vK c) c.ex1 z) (xpar (qv vK c) c.ex2 z) * dlogv (qv vK c) c.ev1 z -
    levalK vK (eulK c.DT) (xpar (qv vK c) c.ev1 z) (xpar (qv vK c) c.ev2 z) *
      pfval (qv vK c) ((c.pfin k l).map fun t => (t.1, t.2.1, vK t.2.2))
        ((c.pinf k l).map fun t => (t.1, vK t.2)) z

omit S in
private theorem pfin_idx (hidx : c.idxCheck = true) (k l : ℕ) :
    (c.pfin k l).all (fun t => decide (t.1 < (qv vK c).length)) = true := by
  simp only [Case.idxCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hidx
  simp only [Case.pfin, qv, List.length_map, List.all_eq_true, decide_eq_true_eq]
  rw [List.getD_eq_getElem?_getD]
  rcases hget : c.PFfinL[k * c.V + l]? with _ | f
  · simp
  · simpa using hidx.1.1.1 f (List.mem_of_getElem? hget)

private theorem idx_facts (hidx : c.idxCheck = true) : c.ev1.length ≤ (qv vK c).length ∧
    c.iz < (qv vK c).length ∧ (qv vK c).getD c.iz 0 = 0 := by
  simp only [Case.idxCheck, Bool.and_eq_true, decide_eq_true_eq] at hidx
  refine ⟨by simpa [qv] using hidx.1.1.2, by simpa [qv] using hidx.1.2, ?_⟩
  have hl : c.iz < c.pts.length := hidx.1.2
  rw [qv, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl,
    Option.map_some, Option.getD_some]
  have h2 := S.isZero _ hidx.2
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some] at h2
  exact h2

private theorem sval_entry (hidx : c.idxCheck = true) (k l : ℕ) (z : F) (hz : ∀ q ∈ qv vK c, z ≠ q) :
    sval vK (qv vK c) z (c.entryS k l) = entryE c vK k l z := by
  obtain ⟨hl, hiz, h0⟩ := idx_facts c S hidx
  simp only [Case.entryS, entryE]
  rw [sval_append S _ z, sval_neg S _ z, sval_mul S _ z hz, sval_mul S _ z hz,
    sval_levK S _ z hz _ _ _ _ _ (by rw [sval_par_inv S _ z hz, sval_par S _ z hz])
      (by rw [sval_par_inv S _ z hz, sval_par S _ z hz]),
    sval_levK S _ z hz _ _ _ _ _ (by rw [sval_par_inv S _ z hz, sval_par S _ z hz])
      (by rw [sval_par_inv S _ z hz, sval_par S _ z hz]),
    sval_par S _ z hz, sval_par S _ z hz, sval_par S _ z hz, sval_par S _ z hz,
    sval_dlog S _ z hz _ hl, sval_pf S _ z hz _ hiz h0 _ _ (pfin_idx c hidx k l)]
  ring

variable [CInv K]

private theorem okAt_hw (q : ℚ) (i : ℕ) (hi : i < (qv vK c).length) :
    vK ((c.wsAt q).getD i Comp.zero) = (q : F) - (qv vK c).getD i 0 := by
  simp only [qv, List.length_map] at hi
  simp [Case.wsAt, qv, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
    S.add, S.neg, S.ofQ, sub_eq_add_neg]

private theorem okAt_inv (q : ℚ) (h : c.okAt q = true) (i : ℕ) (hi : i < (c.wsAt q).length) :
    vK (CInv.inv (c.wsAt q)[i]) = (vK (c.wsAt q)[i])⁻¹ ∧ vK (c.wsAt q)[i] ≠ 0 := by
  simp only [Case.okAt, List.all_eq_true] at h
  exact val_invOK S _ _ (h _ (List.getElem_mem hi))

private theorem okAt_hwi (q : ℚ) (h : c.okAt q = true) (i : ℕ) (hi : i < (qv vK c).length) :
    vK (((c.wsAt q).map CInv.inv).getD i Comp.zero) = ((q : F) - (qv vK c).getD i 0)⁻¹ := by
  have hi' : i < (c.wsAt q).length := by simpa [Case.wsAt, qv] using hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi',
    Option.map_some, Option.getD_some, (okAt_inv c S q h i hi').1,
    ← okAt_hw c S q i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi',
    Option.getD_some]

private theorem okAt_nonpunct (q : ℚ) (h : c.okAt q = true) : ∀ p ∈ qv vK c, (q : F) ≠ p := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  have hw := okAt_hw c S q i hi
  have hi' : i < (c.wsAt q).length := by simpa [Case.wsAt, qv] using hi
  have hne := (okAt_inv c S q h i hi').2
  have hg : (c.wsAt q).getD i Comp.zero = (c.wsAt q)[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
  rw [← hg] at hne
  intro heq
  apply hne
  rw [hw, sub_eq_zero, heq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

private theorem point_entry (hidx : c.idxCheck = true) (q : ℚ) (h : c.pointOK q = true) (k l : ℕ)
    (hk : k < c.V) (hl : l < c.V) : entryE c vK k l (q : F) = 0 := by
  obtain ⟨hlen, hiz, h0⟩ := idx_facts c S hidx
  simp only [Case.pointOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨hok, h⟩ := h
  have h := S.isZero _ (h k hk l hl)
  have hw := okAt_hw c S q
  have hwi := okAt_hwi c S q hok
  have hzc : ∀ p ∈ qv vK c, (q : F) ≠ p := okAt_nonpunct c S q hok
  have hl1 : (c.wsAt q).length = (qv vK c).length := by simp [Case.wsAt, qv]
  have hl2 : ((c.wsAt q).map CInv.inv).length = (qv vK c).length := by simp [Case.wsAt, qv]
  have P := fun es => val_pvP S (qv vK c) (q : F) (c.wsAt q) ((c.wsAt q).map CInv.inv) hl1 hl2
    hw hwi es
  have hid : ∀ k : K, vK (id k) = vK k := fun _ => rfl
  rw [S.add, S.neg, S.mul, S.mul,
    val_levK S vK id hid _ _ _ _ _ (by rw [P, P, pe_neg _ _ hzc]) (by rw [P, P, pe_neg _ _ hzc]),
    val_levK S vK id hid _ _ _ _ _ (by rw [P, P, pe_neg _ _ hzc]) (by rw [P, P, pe_neg _ _ hzc]),
    P, P, P, P, val_dlogP S (qv vK c) (q : F) _ hwi _ hlen,
    val_pfP S (qv vK c) q _ hwi _ _ (pfin_idx c hidx k l)] at h
  simp only [entryE, xpar_eq_pe]
  linear_combination h

/-- **Sats C (partialbråken).** För varje post `(k, l)` och varje `z` utanför punkteringarna:
`A_{kl}(x(z)) · (v₁'/v₁)(z) = (v₂ ∂_{v₂} D^T)(v(z)) · PF_{kl}(z)`. -/
theorem partial_fractions_gen (hidx : c.idxCheck = true) (hdeg : ∀ k < c.V, c.degRow k = true)
    (hpt : ∀ j < c.dmax + 1, c.pointOK ((j : ℚ) + 2) = true)
    (k l : Fin c.V) (z : F) (hz : ∀ q ∈ qv vK c, z ≠ q) :
    levalK vK (c.A k l) (xpar (qv vK c) c.ex1 z) (xpar (qv vK c) c.ex2 z) * dlogv (qv vK c) c.ev1 z =
      levalK vK (eulK c.DT) (xpar (qv vK c) c.ev1 z) (xpar (qv vK c) c.ev2 z) *
        pfval (qv vK c) ((c.pfin k l).map fun t => (t.1, t.2.1, vK t.2.2))
          ((c.pinf k l).map fun t => (t.1, vK t.2)) z := by
  have hd := hdeg k k.2
  simp only [Case.degRow, List.all_eq_true, List.mem_range] at hd
  have hd2 := hd l l.2
  simp only [Case.degOK, Bool.and_eq_true, decide_eq_true_eq] at hd2
  obtain ⟨hle, hdd⟩ := hd2
  have hnp : ∀ j, j < c.dmax + 1 → ∀ q ∈ qv vK c, ((j : F) + 2) ≠ q := by
    intro j hj
    have h1 := hpt j hj
    simp only [Case.pointOK, Bool.and_eq_true] at h1
    have := okAt_nonpunct c S ((j : ℚ) + 2) h1.1
    simpa using this
  have hv := vanish (v := vK) (qv vK c) (c.entryS k l) (kvecs (c.entryS k l)) c.dmax
    (by simpa [qv] using hle) (by simpa [qv] using hdd)
    (fun j hj => ⟨hnp j hj, by
      rw [sval_entry c S hidx k l _ (hnp j hj)]
      have := point_entry c S hidx ((j : ℚ) + 2) (hpt j hj) k l k.2 l.2
      simpa using this⟩) z hz
  rw [sval_entry c S hidx k l z hz, entryE] at hv
  linear_combination hv

/-- **Sats B (kurvan), punktmetoden.** Samma slutsats som `curve_gen`. -/
theorem curve_gen_pts (hdeg : c.curveDeg = true)
    (hpt : ∀ j < c.dmaxC + 1, c.curveAt ((j : ℚ) + 2) = true) (z : F) (hz : ∀ q ∈ qv vK c, z ≠ q) :
    levalK vK c.D (xpar (qv vK c) c.ex1 z) (xpar (qv vK c) c.ex2 z) = 0 := by
  simp only [Case.curveDeg, Bool.and_eq_true, decide_eq_true_eq] at hdeg
  obtain ⟨hle, hdd⟩ := hdeg
  have hnp : ∀ j, j < c.dmaxC + 1 → ∀ q ∈ qv vK c, ((j : F) + 2) ≠ q := by
    intro j hj
    have h1 := hpt j hj
    simp only [Case.curveAt, Bool.and_eq_true] at h1
    have := okAt_nonpunct c S ((j : ℚ) + 2) h1.1
    simpa using this
  have hsv : ∀ w : F, (∀ q ∈ qv vK c, w ≠ q) → sval vK (qv vK c) w c.curveS =
      levalK vK c.D (xpar (qv vK c) c.ex1 w) (xpar (qv vK c) c.ex2 w) := by
    intro w hw
    simp only [Case.curveS]
    rw [sval_levK S _ w hw _ _ _ _ _ (by rw [sval_par_inv S _ w hw, sval_par S _ w hw])
      (by rw [sval_par_inv S _ w hw, sval_par S _ w hw]), sval_par S _ w hw, sval_par S _ w hw]
  have hv := vanish (v := vK) (qv vK c) c.curveS (kvecs c.curveS) c.dmaxC
    (by simpa [qv] using hle) (by simpa [qv] using hdd)
    (fun j hj => ⟨hnp j hj, by
      rw [hsv _ (hnp j hj)]
      have h1 := hpt j hj
      simp only [Case.curveAt, Bool.and_eq_true] at h1
      obtain ⟨hok, h⟩ := h1
      have h := S.isZero _ h
      have hw := okAt_hw c S ((j : ℚ) + 2)
      have hwi := okAt_hwi c S ((j : ℚ) + 2) hok
      have hzc : ∀ p ∈ qv vK c, (((j : ℚ) + 2 : ℚ) : F) ≠ p := okAt_nonpunct c S _ hok
      have hl1 : (c.wsAt ((j : ℚ) + 2)).length = (qv vK c).length := by simp [Case.wsAt, qv]
      have hl2 : ((c.wsAt ((j : ℚ) + 2)).map CInv.inv).length = (qv vK c).length := by
        simp [Case.wsAt, qv]
      have P := fun es => val_pvP S (qv vK c) _ (c.wsAt ((j : ℚ) + 2))
        ((c.wsAt ((j : ℚ) + 2)).map CInv.inv) hl1 hl2 hw hwi es
      have hid : ∀ k : K, vK (id k) = vK k := fun _ => rfl
      rw [val_levK S vK id hid _ _ _ _ _ (by rw [P, P, pe_neg _ _ hzc]) (by rw [P, P, pe_neg _ _ hzc]),
        P, P] at h
      simp only [xpar_eq_pe]
      simpa using h⟩) z hz
  rw [hsv z hz] at hv
  exact hv

end Thms

end X
end LeanResidy
