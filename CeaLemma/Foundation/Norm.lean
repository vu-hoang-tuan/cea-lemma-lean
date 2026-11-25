import CeaLemma.Foundation.VectorSpace

/-!
# A norm over our own vector-space structure

No Mathlib `NormedAddCommGroup`, `NormedSpace`, or `norm` operation.
Only the non-negativity property needed for the Céa derivation is required.
-/

namespace Cea

universe u

structure VectorNorm {V : Type u} (E : VectorSpace V) where
  norm : V → ℝ
  norm_nonneg : ∀ x : V, 0 ≤ norm x

end Cea
