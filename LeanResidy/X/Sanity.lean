import Mathlib.Data.Real.Sqrt
import LeanResidy.X.Casef2a
import LeanResidy.X.Case3122t
import LeanResidy.X.Case488u

/-!
# Rimlighetskontroller: hypoteserna går att uppfylla i ℂ

Satserna i `Case*.lean` har hypoteser om rötterna (`r² = A` osv.) och, för viktfallen, om parametern
(`u ∉ tpts`). Här visas att hypoteserna är uppfyllda för konkreta val i ℂ, så att satserna inte är tomma:
* [3².6²; 3.6.3.6]: `r = i`, `s = √2`, `t = √3`;
* 3.12² med vikt t: `r = i√3`, `s = i`, `t = 1` (lika vikter);
* 4.8²: `r = i`, `s = i√2`, `u = (3 + 4i)/5` (en punkt på enhetscirkeln, ingen enhetsrot).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

open Complex

namespace LeanResidy.X

theorem sqrt_sq_C (a : ℝ) (ha : 0 ≤ a) : ((Real.sqrt a : ℝ) : ℂ) ^ 2 = (a : ℂ) := by
  rw [← ofReal_pow, Real.sq_sqrt ha]

example : Sound (Cf2a.vK (F := ℂ) I (Real.sqrt 2) (Real.sqrt 3)) :=
  Cf2a.sound I _ _ (by simp [I_sq]) (by rw [sqrt_sq_C 2 (by norm_num)]; norm_num)
    (by rw [sqrt_sq_C 3 (by norm_num)]; norm_num)

example : Sound (C3122t.vK (F := ℂ) (I * Real.sqrt 3) I 1) := by
  refine C3122t.sound _ _ _ ?_ (by simp [I_sq]) ?_
  · rw [mul_pow, I_sq, sqrt_sq_C 3 (by norm_num)]; norm_num
  · intro p hp
    simp only [C3122t.tpts, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [Z4.val] <;> norm_num

example : Sound (C488u.vK (F := ℂ) I (I * Real.sqrt 2) ((3 + 4 * I) / 5)) := by
  refine C488u.sound _ _ _ (by simp [I_sq]) ?_ ?_
  · rw [mul_pow, I_sq, sqrt_sq_C 2 (by norm_num)]; norm_num
  · simp only [C488u.tpts, List.forall_mem_cons, List.forall_mem_nil, and_true]
    refine ⟨?_, ?_⟩ <;> (repeat' constructor) <;>
    · simp only [Z4.val, Complex.ext_iff, ne_eq, not_and_or]
      norm_num

end LeanResidy.X
