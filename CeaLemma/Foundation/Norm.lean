import CeaLemma.Foundation.VectorSpace

/-!
# A norm over our own vector-space structure

No Mathlib `NormedAddCommGroup`, `NormedSpace`, or `norm` operation.
The positivity, homogeneity, and triangle properties are stated explicitly.
-/

namespace Cea

universe u

structure VectorNorm {V : Type u} (E : VectorSpace V) where
  norm : V → ℝ
  norm_nonneg : ∀ x : V, 0 ≤ norm x
  norm_eq_zero_iff : ∀ x : V, norm x = 0 ↔ x = E.zero
  norm_smul : ∀ (a : ℝ) (x : V), norm (E.smul a x) = |a| * norm x
  norm_triangle : ∀ x y : V, norm (E.add x y) ≤ norm x + norm y

end Cea
