import LeanResidy.Basic

/-!
# Laplacianen för ett periodiskt gitter och den rationella parametriseringen

* `lapMat V E x₁ x₂` är den viktade laplacianen M(x) på kvotgrafen med `V` noder och kantlista `E`
  (kant `(i, j, n₁, n₂, w)`: vikt `w`, från nod `i` till nod `j` i cellen förskjuten `(n₁, n₂)`), precis
  som i Python-koden (`resmaskin.lap`):
  `M[i,i] += w, M[j,j] += w, M[i,j] -= w x^n, M[j,i] -= w x^{-n}`.
* `xpar qs es z = ∏ (z − qₗ)^{eₗ}` är en monomiell rationell parametrisering.
-/

set_option linter.unusedSimpArgs false

namespace LeanResidy

abbrev Edge := ℕ × ℕ × ℤ × ℤ × ℚ

variable {F : Type} [Field F]

/-- bidraget från en kant till post `(i, j)` -/
def edgeC (x1 x2 : F) (i j : ℕ) (e : Edge) : F :=
  let a := e.1; let b := e.2.1; let n1 := e.2.2.1; let n2 := e.2.2.2.1; let w : F := e.2.2.2.2
  (if i = a ∧ j = a then w else 0) + (if i = b ∧ j = b then w else 0)
    - (if i = a ∧ j = b then w * (x1 ^ n1 * x2 ^ n2) else 0)
    - (if i = b ∧ j = a then w * (x1 ^ n1 * x2 ^ n2)⁻¹ else 0)

/-- Laplacianen M(x₁, x₂). -/
def lapMat (V : ℕ) (E : List Edge) (x1 x2 : F) : Matrix (Fin V) (Fin V) F :=
  fun i j => (E.map (edgeC x1 x2 i j)).sum

/-- samma post som Laurentpolynom (data) -/
def edgeL (i j : ℕ) (e : Edge) : LP :=
  let a := e.1; let b := e.2.1; let n1 := e.2.2.1; let n2 := e.2.2.2.1; let w := e.2.2.2.2
  (if i = a ∧ j = a then [((0, 0), w)] else []) ++ (if i = b ∧ j = b then [((0, 0), w)] else [])
    ++ (if i = a ∧ j = b then [((n1, n2), -w)] else [])
    ++ (if i = b ∧ j = a then [((-n1, -n2), -w)] else [])

def lapL (E : List Edge) (i j : ℕ) : LP := E.flatMap (edgeL i j)

theorem edgeC_eq (x1 x2 : F) (i j : ℕ) (e : Edge) :
    edgeC x1 x2 i j e = leval (edgeL i j e) x1 x2 := by
  simp only [edgeC, edgeL, leval_append]
  split_ifs <;> simp [leval, zpow_neg, mul_inv] <;> ring

theorem lapMat_eq (V : ℕ) (E : List Edge) (x1 x2 : F) (i j : Fin V) :
    lapMat V E x1 x2 i j = leval (lapL E i j) x1 x2 := by
  simp only [lapMat, lapL]
  induction E with
  | nil => simp [leval]
  | cons e E ih => simp [List.flatMap_cons, leval_append, edgeC_eq, ih]

/-- Den monomiella parametriseringen `∏ₗ (z − qₗ)^{eₗ}`. -/
def xpar (qs : List F) (es : List ℤ) (z : F) : F := (List.zipWith (fun q e => (z - q) ^ e) qs es).prod

/-! ### Modellversionen av parametriseringen -/

section
variable {C : Type} [Comp C] {pts : List C}

def posE (es : List ℤ) : List ℕ := es.map Int.toNat
def negE (es : List ℤ) : List ℕ := es.map (fun e => (-e).toNat)

/-- `∏ (z − qₗ)^{eₗ}` som element i modellen `Fr C pts` -/
def frPar (pts : List C) (es : List ℤ) : Fr C pts := ⟨Fr.fac pts (posE es), negE es⟩

variable {v : C → F} (S : Sound v) (z : F)
include S

theorem val_frPar (es : List ℤ) :
    Fr.val v z (frPar pts es) = xpar (pts.map v) es z := by
  simp only [Fr.val, frPar, Fr.val_fac S]
  induction pts generalizing es with
  | nil => cases es <;> simp [Fr.dval, xpar, posE, negE]
  | cons q ps ih =>
    cases es with
    | nil => simp [Fr.dval, xpar, posE, negE]
    | cons e es =>
      have := ih es
      simp only [posE, negE, List.map_cons, Fr.dval, List.map, xpar, List.zipWith_cons_cons,
        List.prod_cons] at this ⊢
      rw [← this]
      rcases e with n | n
      · simp; ring
      · simp only [Int.toNat_negSucc, Int.neg_negSucc, Int.toNat_natCast, zpow_negSucc, pow_zero,
          one_mul]
        generalize z - v q = w
        ring
end

end LeanResidy
