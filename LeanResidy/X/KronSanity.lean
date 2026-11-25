import LeanResidy.X.FrG

/-!
# Rimlighet: villkoren "ingen nämnarfaktor är noll" går att uppfylla

För rationella parametervärden `a₀, b₀` räknar `evalZ4` ut värdet av ett element i `PK` som ett element
i `ℚ(r, s)` (`Z4`). Om normen av det är ett nollskilt rationellt tal är värdet nollskilt för **varje**
val av rötterna `r`, `s` (`Z4.val_ne_zero`). Kärnan kontrollerar normerna för alla faktorerna i `Dl`
(i fallfilerna), så satserna där är inte tomma.
-/

set_option linter.unusedSectionVars false

namespace LeanResidy
namespace X
open LeanResidy.Comp

variable {A B : ℤ} {Kb S : ℕ}

/-- spökpolynomet utvärderat i rationella `a, b`, som element i `ℚ(r, s)` -/
def ghZ4 (A B : ℤ) (a b : ℚ) (P : GP) : Z4 A B :=
  P.foldr (fun t acc => Comp.add (Comp.mul (⟨t.2.a, t.2.b, t.2.c, t.2.d⟩ : Z4 A B)
    (Comp.ofQ (a ^ t.1.1 * b ^ t.1.2))) acc) Comp.zero

def evalZ4 (a b : ℚ) (x : PK A B Kb S) : Z4 A B :=
  Comp.mul (ghZ4 A B a b x.P) (Comp.ofQ (1 / (x.den : ℚ)))

variable {F : Type} [Field F] [CharZero F]

theorem gval_ghZ4 (r s : F) (hr : r ^ 2 = A) (hs : s ^ 2 = B) (a b : ℚ) (P : GP) :
    gval (a : F) (b : F) r s P = Z4.val r s (ghZ4 A B a b P) := by
  have S := Z4.sound r s hr hs
  induction P with
  | nil => simp [gval, ghZ4, S.zero]
  | cons t P ih =>
    simp only [gval, ghZ4, List.map_cons, List.sum_cons, List.foldr_cons] at ih ⊢
    rw [S.add, S.mul, S.ofQ, ih]
    congr 1
    simp only [Z4.val, I4.val, Rat.cast_intCast, Rat.cast_mul]
    have hp : ∀ (q : ℚ) (n : ℕ), ((q ^ n : ℚ) : F) = (q : F) ^ n := fun q n => by
      simpa using map_pow (Rat.castHom F) q n
    rw [hp, hp]; ring

theorem val_evalZ4 (r s : F) (hr : r ^ 2 = A) (hs : s ^ 2 = B) (a b : ℚ) (x : PK A B Kb S) :
    PK.val (a : F) (b : F) r s x = Z4.val r s (evalZ4 a b x) := by
  have S := Z4.sound r s hr hs
  simp only [PK.val, evalZ4]
  rw [S.mul, S.ofQ, ← gval_ghZ4 r s hr hs]
  push_cast; ring

/-- normtestet för nollskildhet -/
def normOK (z : Z4 A B) : Bool :=
  (Z4.norm z).b == 0 && (Z4.norm z).c == 0 && (Z4.norm z).d == 0 && !((Z4.norm z).a == 0)

theorem val_ne_of_normOK (r s : F) (hr : r ^ 2 = A) (hs : s ^ 2 = B) (a b : ℚ) (x : PK A B Kb S)
    (h : normOK (evalZ4 a b x) = true) : PK.val (a : F) (b : F) r s x ≠ 0 := by
  rw [val_evalZ4 r s hr hs]
  simp only [normOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  exact Z4.val_ne_zero r s hr hs _ ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem dl_ne_of_check (r s : F) (hr : r ^ 2 = A) (hs : s ^ 2 = B) (a b : ℚ) (dl : List (PK A B Kb S))
    (h : dl.all (fun d => normOK (evalZ4 a b d)) = true) :
    ∀ d ∈ dl, PK.val (a : F) (b : F) r s d ≠ 0 := by
  intro d hd
  rw [List.all_eq_true] at h
  exact val_ne_of_normOK r s hr hs a b d (h d hd)

end X
end LeanResidy
