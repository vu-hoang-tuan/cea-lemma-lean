import CeaLemma.Foundation.TrialSpace

/-!
# Own definition of a real bilinear form

Neither `LinearMap` nor `LinearMap.BilinForm` is used. The axioms are
explicit in this record, using the operations of `Cea.VectorSpace`.
-/

namespace Cea

universe u

structure BilinearForm {V : Type u} (E : VectorSpace V) where
  eval : V → V → ℝ
  add_left : ∀ x y z : V, eval (E.add x y) z = eval x z + eval y z
  add_right : ∀ x y z : V, eval x (E.add y z) = eval x y + eval x z

/-- Mathematical continuity assumption on the locally defined form. -/
def HasContinuityBound {V : Type u} {E : VectorSpace V}
    (a : BilinearForm E) (N : VectorNorm E) (M : ℝ) : Prop :=
  ∀ x y : V, |a.eval x y| ≤ M * N.norm x * N.norm y

/-- Mathematical coercivity assumption on the locally defined form. -/
def HasCoercivityBound {V : Type u} {E : VectorSpace V}
    (a : BilinearForm E) (N : VectorNorm E) (alpha : ℝ) : Prop :=
  ∀ x : V, alpha * (N.norm x) ^ 2 ≤ a.eval x x

/-- A right-hand-side functional, also owned by the project. -/
structure LinearFunctional {V : Type u} (E : VectorSpace V) where
  eval : V → ℝ

end Cea
