import LeanResidy.Generic

/-!
# Identiteter för rationella funktioner via gradgräns + punktkontroll

Alla storheter i residybevisen är summor av "monom" `c · ∏ᵢ (z − qᵢ)^{eᵢ}` (`eᵢ ∈ ℤ`) i
punkteringarna `qᵢ`. För en sådan summa `s` gäller:

* (symboliskt, bara exponenter) multiplicerar man med `∏ (z − qᵢ)^{−kᵢ}`, `kᵢ = minₜ eₜᵢ`, blir
  `s` ett polynom `G` av grad `≤ d` (`d` räknas ut ur exponenterna);
* (numeriskt exakt) `s` räknas ut i `d + 1` heltalspunkter `z = 2, 3, …, d + 2` med exakt aritmetik
  i `ℚ(r, s)`.

Är alla värdena noll så är `G = 0` (ett nollskilt polynom av grad ≤ d har högst d nollställen), alltså
`s ≡ 0`. Detta är exakt samma argument som Python-koden använder (gradgräns + punktkontroll).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace LeanResidy
open LeanResidy.Comp Polynomial

variable {A B : ℤ}

/-! ## Invers i ℚ(r, s) via normen -/

namespace Z4

def cp (x : Z4 A B) : Z4 A B := Comp.mul (cr x) (Comp.mul (cs x) (cr (cs x)))
def nrm (x : Z4 A B) : Z4 A B := Comp.mul x (cp x)

/-- normen är ett nollskilt rationellt tal -/
def okInv (x : Z4 A B) : Bool :=
  (nrm x).b == 0 && (nrm x).c == 0 && (nrm x).d == 0 && !((nrm x).a == 0)

def inv (x : Z4 A B) : Z4 A B := Comp.mul (cp x) (Comp.ofQ (nrm x).a⁻¹)

variable {F : Type} [Field F] [CharZero F] (r s : F) (hr : r ^ 2 = A) (hs : s ^ 2 = B)
include hr hs

theorem val_inv (x : Z4 A B) (h : okInv x = true) : val r s (inv x) = (val r s x)⁻¹ := by
  have S := sound r s hr hs
  simp only [okInv, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hn : val r s (nrm x) = ((nrm x).a : F) := by simp [val, h1, h2, h3]
  have hm : val r s x * val r s (cp x) = ((nrm x).a : F) := by rw [← hn, nrm, S.mul]
  have ha : ((nrm x).a : F) ≠ 0 := by exact_mod_cast h4
  have hx : val r s x ≠ 0 := by intro h0; rw [h0, zero_mul] at hm; exact ha hm.symm
  rw [inv, S.mul, S.ofQ]
  push_cast
  field_simp
  linear_combination hm

theorem val_ne_zero' (x : Z4 A B) (h : okInv x = true) : val r s x ≠ 0 := by
  intro h0
  have := val_inv r s hr hs x h
  have S := sound r s hr hs
  simp only [okInv, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  have hn : val r s (nrm x) = ((nrm x).a : F) := by simp [val, h.1.1.1, h.1.1.2, h.1.2]
  have hm : val r s x * val r s (cp x) = ((nrm x).a : F) := by rw [← hn, nrm, S.mul]
  rw [h0, zero_mul] at hm
  exact h.2 (by exact_mod_cast hm.symm)

end Z4

/-! ## Produkter `∏ (z − qᵢ)^{eᵢ}` med exponentlistor (saknade exponenter = 0) -/

variable {F : Type} [Field F]

def pe : List F → List ℤ → F → F
  | [], _, _ => 1
  | q :: qs, e, z => (z - q) ^ (e.headD 0) * pe qs e.tail z

def eadd : List ℤ → List ℤ → List ℤ
  | [], e => e
  | e, [] => e
  | a :: e, b :: e' => (a + b) :: eadd e e'

theorem eadd_headD (e e' : List ℤ) : (eadd e e').headD 0 = e.headD 0 + e'.headD 0 := by
  cases e <;> cases e' <;> simp [eadd]

theorem eadd_nil_right (e : List ℤ) : eadd e [] = e := by cases e <;> rfl

theorem eadd_tail (e e' : List ℤ) : (eadd e e').tail = eadd e.tail e'.tail := by
  cases e <;> cases e' <;> simp [eadd, eadd_nil_right]

theorem pe_nil (qs : List F) (z : F) : pe qs [] z = 1 := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [pe, ih]

theorem pe_eadd (qs : List F) (z : F) (hz : ∀ q ∈ qs, z ≠ q) (e e' : List ℤ) :
    pe qs (eadd e e') z = pe qs e z * pe qs e' z := by
  induction qs generalizing e e' with
  | nil => simp [pe]
  | cons q qs ih =>
    have hq : z - q ≠ 0 := sub_ne_zero.mpr (hz q (by simp))
    simp only [pe, eadd_headD, eadd_tail, zpow_add₀ hq]
    rw [ih (fun q' h => hz q' (by simp [h]))]
    ring

theorem pe_ne_zero (qs : List F) (z : F) (hz : ∀ q ∈ qs, z ≠ q) (e : List ℤ) : pe qs e z ≠ 0 := by
  induction qs generalizing e with
  | nil => simp [pe]
  | cons q qs ih =>
    simp only [pe]
    exact mul_ne_zero (zpow_ne_zero _ (sub_ne_zero.mpr (hz q (by simp))))
      (ih (fun q' h => hz q' (by simp [h])) _)

theorem xpar_eq_pe (qs : List F) (es : List ℤ) (z : F) : xpar qs es z = pe qs es z := by
  induction qs generalizing es with
  | nil => cases es <;> simp [xpar, pe]
  | cons q qs ih =>
    cases es with
    | nil => simp [xpar, pe, pe_nil]
    | cons e es =>
      have := ih es
      simp only [xpar] at this
      simp [xpar, pe, this]

/-- enhetsvektor: exponent `e` på plats `i` -/
def unitE (i : ℕ) (e : ℤ) : List ℤ := List.replicate i 0 ++ [e]

theorem pe_unitE (qs : List F) (z : F) (i : ℕ) (e : ℤ) (hi : i < qs.length) :
    pe qs (unitE i e) z = (z - qs.getD i 0) ^ e := by
  induction i generalizing qs with
  | zero => cases qs with
    | nil => simp at hi
    | cons q qs => simp [unitE, pe, pe_nil]
  | succ i ih => cases qs with
    | nil => simp at hi
    | cons q qs =>
      have := ih qs (by simpa using hi)
      simp only [unitE, List.replicate_succ, List.cons_append] at this ⊢
      simp [pe, this]

/-! ## Monomsummor -/

abbrev Mon (C : Type) := C × List ℤ

section Mon
variable {C : Type} [Comp C]

def smul (s t : List (Mon C)) : List (Mon C) :=
  s.flatMap fun a => t.map fun b => (Comp.mul a.1 b.1, eadd a.2 b.2)

def sneg (s : List (Mon C)) : List (Mon C) := s.map fun a => (Comp.neg a.1, a.2)

def spow (s : List (Mon C)) : ℕ → List (Mon C)
  | 0 => [(Comp.ofQ 1, [])]
  | n + 1 => smul s (spow s n)

def szp (x xi : List (Mon C)) : ℤ → List (Mon C)
  | Int.ofNat n => spow x n
  | Int.negSucc n => spow xi (n + 1)

def slev (L : LP) (x1 x1i x2 x2i : List (Mon C)) : List (Mon C) :=
  L.flatMap fun t => smul [(Comp.ofQ t.2, [])] (smul (szp x1 x1i t.1.1) (szp x2 x2i t.1.2))

def spar (es : List ℤ) : List (Mon C) := [(Comp.ofQ 1, es)]

def sdlog (es : List ℤ) : List (Mon C) :=
  (List.range es.length).map fun i => (Comp.ofQ (es.getD i 0 : ℚ), unitE i (-1))

/-- partialbråket; `iz` är index för punkten 0 -/
def spf (iz : ℕ) (fin : List (ℕ × ℕ × C)) (inf : List (ℕ × C)) : List (Mon C) :=
  fin.map (fun t => (t.2.2, unitE t.1 (-(t.2.1 : ℤ)))) ++ inf.map (fun t => (t.2, unitE iz (t.1 : ℤ)))

variable {v : C → F} (S : Sound v) (qs : List F) (z : F)

def sval (v : C → F) (qs : List F) (z : F) (s : List (Mon C)) : F :=
  (s.map fun m => v m.1 * pe qs m.2 z).sum

include S

theorem sval_append (s t : List (Mon C)) : sval v qs z (s ++ t) = sval v qs z s + sval v qs z t := by
  simp [sval]

theorem sval_neg (s : List (Mon C)) : sval v qs z (sneg s) = - sval v qs z s := by
  induction s with
  | nil => simp [sval, sneg]
  | cons a s ih => simp only [sval, sneg, List.map_cons, List.sum_cons] at *; rw [ih, S.neg]; ring

variable (hz : ∀ q ∈ qs, z ≠ q)
include hz

theorem sval_map_mon (a : Mon C) (t : List (Mon C)) :
    sval v qs z (t.map fun b => (Comp.mul a.1 b.1, eadd a.2 b.2)) =
      (v a.1 * pe qs a.2 z) * sval v qs z t := by
  induction t with
  | nil => simp [sval]
  | cons b t ih =>
    simp only [sval, List.map_cons, List.sum_cons, List.map_map] at ih ⊢
    rw [mul_add, ← ih]
    simp only [Function.comp_def, S.mul, pe_eadd qs z hz]
    ring_nf

theorem sval_mul (s t : List (Mon C)) : sval v qs z (smul s t) = sval v qs z s * sval v qs z t := by
  induction s with
  | nil => simp [sval, smul]
  | cons a s ih =>
    simp only [smul, List.flatMap_cons] at ih ⊢
    rw [sval_append S qs z, ih, sval_map_mon S qs z hz]
    simp only [sval, List.map_cons, List.sum_cons]
    ring

theorem sval_pow (s : List (Mon C)) (n : ℕ) : sval v qs z (spow s n) = sval v qs z s ^ n := by
  induction n with
  | zero => simp [spow, sval, S.ofQ, pe_nil]
  | succ n ih => rw [spow, sval_mul S qs z hz, ih]; ring

theorem sval_zp (x xi : List (Mon C)) (h : sval v qs z xi = (sval v qs z x)⁻¹) (n : ℤ) :
    sval v qs z (szp x xi n) = sval v qs z x ^ n := by
  cases n with
  | ofNat n => simp [szp, sval_pow S qs z hz]
  | negSucc n => simp [szp, sval_pow S qs z hz, h, zpow_negSucc, inv_pow]

theorem sval_lev (L : LP) (x1 x1i x2 x2i : List (Mon C))
    (h1 : sval v qs z x1i = (sval v qs z x1)⁻¹) (h2 : sval v qs z x2i = (sval v qs z x2)⁻¹) :
    sval v qs z (slev L x1 x1i x2 x2i) = leval L (sval v qs z x1) (sval v qs z x2) := by
  induction L with
  | nil => simp [slev, sval, leval]
  | cons t L ih =>
    simp only [slev, List.flatMap_cons] at ih ⊢
    rw [sval_append S qs z, ih, sval_mul S qs z hz, sval_mul S qs z hz, sval_zp S qs z hz _ _ h1,
      sval_zp S qs z hz _ _ h2]
    simp [sval, S.ofQ, pe_nil, leval]
    ring

theorem sval_par (es : List ℤ) : sval v qs z (spar es) = xpar qs es z := by
  simp [sval, spar, S.ofQ, xpar_eq_pe]

theorem sval_par_inv (es : List ℤ) :
    sval v qs z (spar (es.map (- ·))) = (xpar qs es z)⁻¹ := by
  rw [sval_par S qs z hz, xpar_eq_pe, xpar_eq_pe]
  apply eq_inv_of_mul_eq_one_left
  rw [← pe_eadd qs z hz]
  clear hz
  induction qs generalizing es with
  | nil => simp [pe]
  | cons q qs ih =>
    cases es with
    | nil => simp [eadd, pe, pe_nil]
    | cons e es => simp [eadd, pe, ih]

theorem sval_dlog (es : List ℤ) (hl : es.length ≤ qs.length) :
    sval v qs z (sdlog es) = dlogv qs es z := by
  simp only [sval, sdlog, dlogv, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  simp [S.ofQ, pe_unitE qs z i _ (by omega), zpow_neg, div_eq_mul_inv]

theorem sval_pf (iz : ℕ) (hiz : iz < qs.length) (h0 : qs.getD iz 0 = 0)
    (fin : List (ℕ × ℕ × C)) (inf : List (ℕ × C))
    (hfin : fin.all (fun t => decide (t.1 < qs.length)) = true) :
    sval v qs z (spf iz fin inf) =
      pfval qs (fin.map fun t => (t.1, t.2.1, v t.2.2)) (inf.map fun t => (t.1, v t.2)) z := by
  simp only [List.all_eq_true, decide_eq_true_eq] at hfin
  simp only [spf, sval_append S qs z, pfval]
  congr 1
  · simp only [sval, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro t ht
    simp [pe_unitE qs z _ _ (hfin t ht), zpow_neg, div_eq_mul_inv]
  · simp only [sval, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply]
    rw [pe_unitE qs z _ _ hiz, h0, sub_zero, zpow_natCast]

end Mon

/-! ## Gradgräns och nollställen -/

section Deg
variable {T : Type} [Comp T]

def leB : List F → List ℤ → List ℤ → Bool
  | [], _, _ => true
  | _ :: qs, e, k => decide (k.headD 0 ≤ e.headD 0) && leB qs e.tail k.tail

/-- samma kontroll utan kroppen (för kärnan): `kᵢ ≤ eᵢ` för de `n` första platserna -/
def leN : ℕ → List ℤ → List ℤ → Bool
  | 0, _, _ => true
  | n + 1, e, k => decide (k.headD 0 ≤ e.headD 0) && leN n e.tail k.tail

theorem leB_of_leN (qs : List F) (e k : List ℤ) (h : leN qs.length e k = true) : leB qs e k = true := by
  induction qs generalizing e k with
  | nil => rfl
  | cons q qs ih =>
    simp only [leN, List.length_cons, Bool.and_eq_true] at h
    simp only [leB, Bool.and_eq_true]
    exact ⟨h.1, ih _ _ h.2⟩

def degN : ℕ → List ℤ → List ℤ → ℕ
  | 0, _, _ => 0
  | n + 1, e, k => (e.headD 0 - k.headD 0).toNat + degN n e.tail k.tail

def emin : List ℤ → List ℤ → List ℤ
  | [], e => e.map (min 0)
  | e, [] => e.map (min 0)
  | a :: e, b :: e' => min a b :: emin e e'

def kvecs (s : List (Mon T)) : List ℤ := s.foldr (fun a acc => emin a.2 acc) []

def sdeg (n : ℕ) (s : List (Mon T)) (k : List ℤ) : ℕ := s.foldr (fun a acc => max (degN n a.2 k) acc) 0

noncomputable def peX : List F → List ℤ → List ℤ → F[X]
  | [], _, _ => 1
  | q :: qs, e, k => (X - C q) ^ (e.headD 0 - k.headD 0).toNat * peX qs e.tail k.tail

theorem natDegree_peX (qs : List F) (e k : List ℤ) : (peX qs e k).natDegree ≤ degN qs.length e k := by
  induction qs generalizing e k with
  | nil => simp [peX]
  | cons q qs ih =>
    simp only [peX, degN, List.length_cons]
    refine (natDegree_mul_le).trans (add_le_add ?_ (ih _ _))
    refine natDegree_pow_le.trans ?_
    simp [natDegree_X_sub_C]

theorem eval_peX (qs : List F) (z : F) (hz : ∀ q ∈ qs, z ≠ q) (e k : List ℤ) (h : leB qs e k = true) :
    (peX qs e k).eval z * pe qs k z = pe qs e z := by
  induction qs generalizing e k with
  | nil => simp [peX, pe]
  | cons q qs ih =>
    simp only [leB, Bool.and_eq_true, decide_eq_true_eq] at h
    have hq : z - q ≠ 0 := sub_ne_zero.mpr (hz q (by simp))
    simp only [peX, pe, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
    rw [← ih (fun q' h' => hz q' (by simp [h'])) _ _ h.2]
    have hpow : (z - q) ^ e.headD 0 =
        (z - q) ^ (e.headD 0 - k.headD 0).toNat * (z - q) ^ k.headD 0 := by
      rw [← zpow_natCast, ← zpow_add₀ hq, Int.toNat_of_nonneg (by omega)]; ring_nf
    rw [hpow]
    ring

variable {v : T → F}

noncomputable def Gpoly (v : T → F) (qs : List F) (s : List (Mon T)) (k : List ℤ) : F[X] :=
  (s.map fun m => C (v m.1) * peX qs m.2 k).sum

theorem natDegree_Gpoly (qs : List F) (s : List (Mon T)) (k : List ℤ) :
    (Gpoly v qs s k).natDegree ≤ sdeg qs.length s k := by
  induction s with
  | nil => simp [Gpoly, sdeg]
  | cons a s ih =>
    simp only [Gpoly, sdeg, List.map_cons, List.sum_cons, List.foldr_cons] at ih ⊢
    refine (natDegree_add_le _ _).trans (max_le_max ?_ ih)
    exact (natDegree_C_mul_le _ _).trans (natDegree_peX qs _ _)

theorem eval_Gpoly (qs : List F) (z : F) (hz : ∀ q ∈ qs, z ≠ q) (s : List (Mon T)) (k : List ℤ)
    (h : s.all (fun m => leN qs.length m.2 k) = true) :
    (Gpoly v qs s k).eval z * pe qs k z = sval v qs z s := by
  induction s with
  | nil => simp [Gpoly, sval]
  | cons a s ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [Gpoly, sval, List.map_cons, List.sum_cons, eval_add, eval_mul, eval_C] at ih ⊢
    rw [add_mul, ih h.2, mul_assoc, eval_peX qs z hz _ _ (leB_of_leN qs _ _ h.1)]

variable [CharZero F]

/-- **Huvudlemmat.** Gradgräns + `d + 1` exakta punktvärden ⇒ identiskt noll. -/
theorem vanish (qs : List F) (s : List (Mon T)) (k : List ℤ) (d : ℕ)
    (hle : s.all (fun m => leN qs.length m.2 k) = true) (hd : sdeg qs.length s k ≤ d)
    (hpt : ∀ j : ℕ, j < d + 1 → (∀ q ∈ qs, ((j : F) + 2) ≠ q) ∧ sval v qs ((j : F) + 2) s = 0)
    (z : F) (hz : ∀ q ∈ qs, z ≠ q) : sval v qs z s = 0 := by
  have hG : Gpoly v qs s k = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero (Gpoly v qs s k)
      (f := fun j : Fin (d + 1) => ((j : ℕ) : F) + 2) ?_ ?_ ?_
    · intro a b hab
      simp only [add_left_inj, Nat.cast_inj] at hab
      exact Fin.ext hab
    · intro j
      obtain ⟨hq, h0⟩ := hpt j j.2
      have := eval_Gpoly (v := v) qs _ hq s k hle
      rw [h0] at this
      exact (mul_eq_zero.mp this).resolve_right (pe_ne_zero qs _ hq k)
    · simp only [Fintype.card_fin]
      exact Nat.lt_succ_of_le ((natDegree_Gpoly qs s k).trans hd)
  rw [← eval_Gpoly qs z hz s k hle, hG, eval_zero, zero_mul]

end Deg

/-! ## Exakt evaluering i en punkt -/

section Point
variable {C : Type} [Comp C]

/-- `∏ wᵢ^{eᵢ}` med `wiᵢ = wᵢ⁻¹` -/
def pvP : List C → List C → List ℤ → C
  | w :: ws, wi :: wis, es => Comp.mul (zp w wi (es.headD 0)) (pvP ws wis es.tail)
  | _, _, _ => Comp.ofQ 1

def dlogP (es : List ℤ) (wi : List C) : C :=
  sumC ((List.range es.length).map fun i => Comp.mul (Comp.ofQ (es.getD i 0 : ℚ)) (wi.getD i Comp.zero))

def pfP (c : ℚ) (fin : List (ℕ × ℕ × C)) (inf : List (ℕ × C)) (wi : List C) : C :=
  Comp.add (sumC (fin.map fun t => Comp.mul t.2.2 (npow (wi.getD t.1 Comp.zero) t.2.1)))
    (sumC (inf.map fun t => Comp.mul t.2 (npow (Comp.ofQ c) t.1)))

variable {v : C → F} (S : Sound v)
include S

theorem val_pvP (qs : List F) (z : F) (ws wis : List C) (hl : ws.length = qs.length)
    (hl' : wis.length = qs.length)
    (hw : ∀ i < qs.length, v (ws.getD i Comp.zero) = z - qs.getD i 0)
    (hwi : ∀ i < qs.length, v (wis.getD i Comp.zero) = (z - qs.getD i 0)⁻¹) (es : List ℤ) :
    v (pvP ws wis es) = pe qs es z := by
  induction qs generalizing ws wis es with
  | nil =>
    cases ws <;> cases wis <;> simp_all [pvP, pe, S.ofQ]
  | cons q qs ih =>
    cases ws with
    | nil => simp at hl
    | cons w ws =>
      cases wis with
      | nil => simp at hl'
      | cons wi wis =>
        simp only [pvP, pe, S.mul]
        have h0 := hw 0 (by simp); have h0' := hwi 0 (by simp)
        simp only [List.getD_cons_zero] at h0 h0'
        rw [val_zp S w wi (by rw [h0, h0']), h0,
          ih ws wis (by simpa using hl) (by simpa using hl')
            (fun i hi => by simpa using hw (i + 1) (by simpa using hi))
            (fun i hi => by simpa using hwi (i + 1) (by simpa using hi))]

theorem val_dlogP (qs : List F) (z : F) (wis : List C)
    (hwi : ∀ i < qs.length, v (wis.getD i Comp.zero) = (z - qs.getD i 0)⁻¹) (es : List ℤ)
    (hl : es.length ≤ qs.length) : v (dlogP es wis) = dlogv qs es z := by
  simp only [dlogP, val_sumC S, List.map_map, dlogv]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  simp only [Function.comp_apply, S.mul, S.ofQ, hwi i (by omega), Rat.cast_intCast, div_eq_mul_inv]

theorem val_pfP (qs : List F) (c : ℚ) (wis : List C)
    (hwi : ∀ i < qs.length, v (wis.getD i Comp.zero) = ((c : F) - qs.getD i 0)⁻¹)
    (fin : List (ℕ × ℕ × C)) (inf : List (ℕ × C))
    (hfin : fin.all (fun t => decide (t.1 < qs.length)) = true) :
    v (pfP c fin inf wis) =
      pfval qs (fin.map fun t => (t.1, t.2.1, v t.2.2)) (inf.map fun t => (t.1, v t.2)) (c : F) := by
  simp only [List.all_eq_true, decide_eq_true_eq] at hfin
  simp only [pfP, S.add, val_sumC S, List.map_map, pfval]
  congr 1
  · apply congrArg List.sum
    apply List.map_congr_left
    intro t ht
    simp only [Function.comp_apply, S.mul, val_npow S, hwi _ (hfin t ht), inv_pow, div_eq_mul_inv]
  · apply congrArg List.sum
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply, S.mul, val_npow S, S.ofQ]

end Point

theorem pe_neg (qs : List F) (z : F) (hz : ∀ q ∈ qs, z ≠ q) (es : List ℤ) :
    pe qs (es.map (- ·)) z = (pe qs es z)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pe_eadd qs z hz]
  clear hz
  induction qs generalizing es with
  | nil => simp [pe]
  | cons q qs ih =>
    cases es with
    | nil => simp [eadd, pe, pe_nil]
    | cons e es => simp [eadd, pe, ih]

/-! ## Punktdata i ℚ(r, s) -/

section PointZ4
variable {A B : ℤ}

def wsAt (pts : List (Z4 A B)) (c : ℚ) : List (Z4 A B) :=
  pts.map fun q => Comp.add (Comp.ofQ c) (Comp.neg q)

def okAt (pts : List (Z4 A B)) (c : ℚ) : Bool := (wsAt pts c).all Z4.okInv

variable [CharZero F] (r s : F) (hr : r ^ 2 = A) (hs : s ^ 2 = B) (pts : List (Z4 A B)) (c : ℚ)
include hr hs

theorem okAt_hw (i : ℕ) (hi : i < (pts.map (Z4.val r s)).length) :
    Z4.val r s ((wsAt pts c).getD i Comp.zero) = (c : F) - (pts.map (Z4.val r s)).getD i 0 := by
  have S := Z4.sound r s hr hs
  simp only [List.length_map] at hi
  simp [wsAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi, S.add,
    S.neg, S.ofQ, sub_eq_add_neg]

theorem okAt_hwi (h : okAt pts c = true) (i : ℕ) (hi : i < (pts.map (Z4.val r s)).length) :
    Z4.val r s (((wsAt pts c).map Z4.inv).getD i Comp.zero) =
      ((c : F) - (pts.map (Z4.val r s)).getD i 0)⁻¹ := by
  have hi' : i < (wsAt pts c).length := by simpa [wsAt] using hi
  simp only [okAt, List.all_eq_true] at h
  have hmem : (wsAt pts c)[i] ∈ wsAt pts c := List.getElem_mem hi'
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi',
    Option.map_some, Option.getD_some, Z4.val_inv r s hr hs _ (h _ hmem),
    ← okAt_hw r s hr hs pts c i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi',
    Option.getD_some]

theorem okAt_nonpunct (h : okAt pts c = true) : ∀ q ∈ pts.map (Z4.val r s), (c : F) ≠ q := by
  intro q hq
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
  have hw := okAt_hw r s hr hs pts c i hi
  simp only [okAt, List.all_eq_true] at h
  have hi' : i < (wsAt pts c).length := by simpa [wsAt] using hi
  have hne := Z4.val_ne_zero' r s hr hs _ (h _ (List.getElem_mem hi'))
  have hg : (wsAt pts c).getD i Comp.zero = (wsAt pts c)[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
  rw [← hg] at hne
  intro heq
  apply hne
  rw [hw, sub_eq_zero, heq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

end PointZ4

end LeanResidy
