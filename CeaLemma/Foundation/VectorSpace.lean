import CeaLemma.Foundation.Real

/-!
# An axiomatic real vector space, defined by this project

The eight fields ending in `_axiom` are the vector-space axioms.
No `Module`, `AddCommGroup` or `NormedSpace` type class is assumed.
An abstract vector space has AXIOMS rather than proofs of the axioms;
a concrete model proving them is supplied in `Examples/RealLine.lean`.
-/

namespace Cea

universe u

structure VectorSpace (V : Type u) where
  add : V → V → V
  zero : V
  neg : V → V
  smul : ℝ → V → V
  add_assoc_axiom : ∀ x y z : V, add (add x y) z = add x (add y z)
  add_comm_axiom : ∀ x y : V, add x y = add y x
  zero_add_axiom : ∀ x : V, add zero x = x
  add_left_neg_axiom : ∀ x : V, add x (neg x) = zero
  one_smul_axiom : ∀ x : V, smul 1 x = x
  mul_smul_axiom : ∀ (a b : ℝ) (x : V), smul (a * b) x = smul a (smul b x)
  add_smul_axiom : ∀ (a b : ℝ) (x : V), smul (a + b) x = add (smul a x) (smul b x)
  smul_add_axiom : ∀ (a : ℝ) (x y : V), smul a (add x y) = add (smul a x) (smul a y)

namespace VectorSpace

variable {V : Type u} (E : VectorSpace V)

/-- Subtraction is defined, not imported. -/
def sub (x y : V) : V := E.add x (E.neg y)

/-- Derive the right zero law from commutativity and the left zero axiom. -/
theorem add_zero (x : V) : E.add x E.zero = x := by
  calc
    E.add x E.zero = E.add E.zero x := E.add_comm_axiom x E.zero
    _ = x := E.zero_add_axiom x

/-- Derive cancellation in the reverse order. -/
theorem neg_add_cancel (x : V) : E.add (E.neg x) x = E.zero := by
  calc
    E.add (E.neg x) x = E.add x (E.neg x) := E.add_comm_axiom (E.neg x) x
    _ = E.zero := E.add_left_neg_axiom x

/-- Subtracting a vector from itself gives zero. -/
theorem sub_self (x : V) : E.sub x x = E.zero := by
  change E.add x (E.neg x) = E.zero
  exact E.add_left_neg_axiom x

/-- First derived cancellation law. -/
theorem sub_add_cancel (x y : V) : E.add (E.sub x y) y = x := by
  change E.add (E.add x (E.neg y)) y = x
  calc
    E.add (E.add x (E.neg y)) y = E.add x (E.add (E.neg y) y) :=
      E.add_assoc_axiom x (E.neg y) y
    _ = E.add x E.zero := by rw [E.neg_add_cancel y]
    _ = x := E.add_zero x

/-- Moving a subtraction through a sum. -/
theorem add_sub (x y z : V) :
    E.add x (E.sub y z) = E.sub (E.add x y) z := by
  change E.add x (E.add y (E.neg z)) = E.add (E.add x y) (E.neg z)
  exact (E.add_assoc_axiom x y (E.neg z)).symm

/-- Error decomposition, proved only from our vector-space axioms. -/
theorem sub_split (u uh vh : V) :
    E.sub u uh = E.add (E.sub u vh) (E.sub vh uh) := by
  have h : E.add (E.sub u vh) (E.sub vh uh) = E.sub u uh := by
    calc
      E.add (E.sub u vh) (E.sub vh uh) =
          E.sub (E.add (E.sub u vh) vh) uh :=
        E.add_sub (E.sub u vh) vh uh
      _ = E.sub u uh := by rw [E.sub_add_cancel u vh]
  exact h.symm

end VectorSpace
end Cea
