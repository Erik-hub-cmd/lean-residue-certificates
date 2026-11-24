import LeanResidy.Points

/-!
# Utvidgning: modeller med kontrollerad invers och kvadratiska utvidgningar

* `invOK w wi`: kärnan kontrollerar `w · wi = 1` i modellen; då är `val wi = (val w)⁻¹` och `val w ≠ 0`
  för varje sund tolkning. Inversen själv (`CInv.inv`) behöver alltså inte bevisas korrekt.
* `Quad C a`: modellen `C[t]/(t² − a)`, element `x + y·t`. Med `Z4 A B` som bas ger det
  `ℚ(r, s, t)` av grad 8 (`Z8`), t.ex. `ℚ(i, √2, √3)`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace LeanResidy
namespace X
open LeanResidy.Comp

/-- en (okontrollerad) invers i modellen -/
class CInv (C : Type) where
  inv : C → C

/-- kontrollen `w · wi − 1 = 0` -/
def invOK {C : Type} [Comp C] (w wi : C) : Bool :=
  Comp.isZero (Comp.add (Comp.mul w wi) (Comp.neg (Comp.ofQ 1)))

theorem val_invOK {C : Type} [Comp C] {F : Type} [Field F] {v : C → F} (S : Sound v) (w wi : C)
    (h : invOK w wi = true) : v wi = (v w)⁻¹ ∧ v w ≠ 0 := by
  have h0 := S.isZero _ h
  rw [S.add, S.mul, S.neg, S.ofQ] at h0
  have h1 : v w * v wi = 1 := by push_cast at h0; linear_combination h0
  exact ⟨eq_inv_of_mul_eq_one_right h1, left_ne_zero_of_mul_eq_one h1⟩

instance {A B : ℤ} : CInv (Z4 A B) := ⟨Z4.inv⟩
instance : CInv ℚ := ⟨fun q => q⁻¹⟩


/-! ## Invers i modellen av rationella funktioner `Fr C pts` (okontrollerad, se `invOK`)

Konstanter och linjära täljare `a₀ + a₁·u` vars rot finns bland `pts` inverteras; allt annat ger 0
(och då misslyckas kontrollen `invOK`). -/

def findIdx {C : Type} [Comp C] (pts : List C) (ρ : C) : Option ℕ :=
  (List.range pts.length).find? fun j => Comp.isZero (Comp.add (pts.getD j Comp.zero) (Comp.neg ρ))

instance {C : Type} [Comp C] [CInv C] {pts : List C} : CInv (Fr C pts) where
  inv x := match x.num with
    | [c] => ⟨P.scale (CInv.inv c) (Fr.fac pts x.k), []⟩
    | [a0, a1] =>
      let ia1 := CInv.inv a1
      match findIdx pts (Comp.neg (Comp.mul a0 ia1)) with
      | some j => ⟨P.scale ia1 (Fr.fac pts x.k), kvec j 1⟩
      | none => ⟨[], []⟩
    | _ => ⟨[], []⟩

/-! ## Kvadratisk utvidgning -/

/-- `x + y·t`, `t² = a` -/
structure Quad (C : Type) (a : C) where
  x : C
  y : C

instance {C : Type} [Comp C] {a : C} : Comp (Quad C a) where
  zero := ⟨Comp.zero, Comp.zero⟩
  add p q := ⟨Comp.add p.x q.x, Comp.add p.y q.y⟩
  mul p q := ⟨Comp.add (Comp.mul p.x q.x) (Comp.mul a (Comp.mul p.y q.y)),
              Comp.add (Comp.mul p.x q.y) (Comp.mul p.y q.x)⟩
  neg p := ⟨Comp.neg p.x, Comp.neg p.y⟩
  ofQ q := ⟨Comp.ofQ q, Comp.zero⟩
  isZero p := Comp.isZero p.x && Comp.isZero p.y

/-- `(x + y t)⁻¹ = (x − y t)·(x² − a y²)⁻¹` -/
instance {C : Type} [Comp C] [CInv C] {a : C} : CInv (Quad C a) where
  inv p := let n := CInv.inv (Comp.add (Comp.mul p.x p.x) (Comp.neg (Comp.mul a (Comp.mul p.y p.y))))
    ⟨Comp.mul p.x n, Comp.neg (Comp.mul p.y n)⟩

namespace Quad
variable {C : Type} [Comp C] {a : C} {F : Type} [Field F]

def val (v : C → F) (t : F) (p : Quad C a) : F := v p.x + v p.y * t

theorem sound {v : C → F} (S : Sound v) (t : F) (ht : t ^ 2 = v a) :
    Sound (val (a := a) v t) where
  zero := by simp [val, Comp.zero, S.zero]
  add p q := by simp only [val, Comp.add, S.add]; ring
  mul p q := by
    simp only [val, Comp.mul, S.add, S.mul]
    linear_combination (-(v p.y * v q.y)) * ht
  neg p := by simp only [val, Comp.neg, S.neg]; ring
  ofQ q := by simp [val, Comp.ofQ, S.ofQ, S.zero]
  isZero p h := by
    simp only [Comp.isZero, Bool.and_eq_true] at h
    simp [val, S.isZero _ h.1, S.isZero _ h.2]

end Quad

/-- `ℚ(r, s, t)`, `r² = A`, `s² = B`, `t² = c` -/
abbrev Z8 (A B : ℤ) (c : ℚ) := Quad (Z4 A B) (⟨c, 0, 0, 0⟩ : Z4 A B)

/-- tolkningen `x + y·t` med `x, y ∈ ℚ(r, s)` -/
def Z8.val {A B : ℤ} {c : ℚ} {F : Type} [Field F] (r s t : F) : Z8 A B c → F :=
  Quad.val (Z4.val r s) t

theorem Z8.sound {A B : ℤ} {c : ℚ} {F : Type} [Field F] [CharZero F] (r s t : F)
    (hr : r ^ 2 = A) (hs : s ^ 2 = B) (ht : t ^ 2 = c) : Sound (Z8.val (A := A) (B := B) (c := c) r s t) :=
  Quad.sound (Z4.sound r s hr hs) t (by simp [Z4.val, ht])

end X
end LeanResidy
