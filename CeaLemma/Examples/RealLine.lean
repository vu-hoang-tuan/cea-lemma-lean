import CeaLemma.Foundation.Norm

/-!
# Concrete verification: the real line is a normed real vector space

Unlike an abstract record, this example PROVES all eight vector-space
axioms and the norm axioms for concrete data using only the permitted
real-number foundation.
-/

namespace Cea.Examples

/-- The one-dimensional real vector space. -/
def realLine : Cea.VectorSpace ℝ where
  add := fun x y => x + y
  zero := 0
  neg := fun x => -x
  smul := fun a x => a * x
  add_assoc_axiom := by
    intro x y z
    exact add_assoc x y z
  add_comm_axiom := by
    intro x y
    exact add_comm x y
  zero_add_axiom := by
    intro x
    exact zero_add x
  add_left_neg_axiom := by
    intro x
    exact add_neg_cancel x
  one_smul_axiom := by
    intro x
    exact one_mul x
  mul_smul_axiom := by
    intro a b x
    exact mul_assoc a b x
  add_smul_axiom := by
    intro a b x
    exact add_mul a b x
  smul_add_axiom := by
    intro a x y
    exact mul_add a x y

/-- Absolute value is a norm on our locally defined real vector space. -/
def realAbs : Cea.VectorNorm realLine where
  norm := fun x => |x|
  norm_nonneg := by
    intro x
    exact abs_nonneg x
  norm_eq_zero_iff := by
    intro x
    exact abs_eq_zero
  norm_smul := by
    intro a x
    exact abs_mul a x
  norm_triangle := by
    intro x y
    exact abs_add_le x y

-- This checks a concrete realization of the abstract vector-space structure.
#check realLine
#check realAbs

end Cea.Examples
