import CeaLemma.Bilinear.Definition

/-!
# Derive the minus rules of a bilinear form from its own axioms.

This is not a re-export of `LinearMap.BilinForm.sub_left`/`sub_right`.
-/

namespace Cea

universe u

namespace BilinearForm

variable {V : Type u} {E : VectorSpace V}

/-- The first zero law follows from additivity (not an extra axiom). -/
theorem zero_left (a : BilinearForm E) (y : V) : a.eval E.zero y = 0 := by
  have h : a.eval E.zero y = a.eval E.zero y + a.eval E.zero y := by
    calc
      a.eval E.zero y = a.eval (E.add E.zero E.zero) y := by
        rw [E.zero_add_axiom E.zero]
      _ = a.eval E.zero y + a.eval E.zero y :=
        a.add_left E.zero E.zero y
  have hsum : a.eval E.zero y + a.eval E.zero y = a.eval E.zero y + 0 := by
    calc
      a.eval E.zero y + a.eval E.zero y = a.eval E.zero y := h.symm
      _ = a.eval E.zero y + 0 := (add_zero _).symm
  exact add_left_cancel hsum

/-- The second zero law follows from additivity. -/
theorem zero_right (a : BilinearForm E) (x : V) : a.eval x E.zero = 0 := by
  have h : a.eval x E.zero = a.eval x E.zero + a.eval x E.zero := by
    calc
      a.eval x E.zero = a.eval x (E.add E.zero E.zero) := by
        rw [E.zero_add_axiom E.zero]
      _ = a.eval x E.zero + a.eval x E.zero :=
        a.add_right x E.zero E.zero
  have hsum : a.eval x E.zero + a.eval x E.zero = a.eval x E.zero + 0 := by
    calc
      a.eval x E.zero + a.eval x E.zero = a.eval x E.zero := h.symm
      _ = a.eval x E.zero + 0 := (add_zero _).symm
  exact add_left_cancel hsum

/-- Additive inverses in the first argument. -/
theorem neg_left (a : BilinearForm E) (x z : V) :
    a.eval (E.neg x) z = -(a.eval x z) := by
  have hz : a.eval (E.neg x) z + a.eval x z = 0 := by
    calc
      a.eval (E.neg x) z + a.eval x z = a.eval (E.add (E.neg x) x) z :=
        (a.add_left (E.neg x) x z).symm
      _ = a.eval E.zero z := by rw [E.neg_add_cancel x]
      _ = 0 := a.zero_left z
  calc
    a.eval (E.neg x) z = a.eval (E.neg x) z + 0 := (add_zero _).symm
    _ = a.eval (E.neg x) z + (a.eval x z + -(a.eval x z)) := by
      rw [add_neg_cancel]
    _ = (a.eval (E.neg x) z + a.eval x z) + -(a.eval x z) :=
      (add_assoc _ _ _).symm
    _ = 0 + -(a.eval x z) := by rw [hz]
    _ = -(a.eval x z) := zero_add _

/-- Additive inverses in the second argument. -/
theorem neg_right (a : BilinearForm E) (x z : V) :
    a.eval z (E.neg x) = -(a.eval z x) := by
  have hz : a.eval z (E.neg x) + a.eval z x = 0 := by
    calc
      a.eval z (E.neg x) + a.eval z x = a.eval z (E.add (E.neg x) x) :=
        (a.add_right z (E.neg x) x).symm
      _ = a.eval z E.zero := by rw [E.neg_add_cancel x]
      _ = 0 := a.zero_right z
  calc
    a.eval z (E.neg x) = a.eval z (E.neg x) + 0 := (add_zero _).symm
    _ = a.eval z (E.neg x) + (a.eval z x + -(a.eval z x)) := by
      rw [add_neg_cancel]
    _ = (a.eval z (E.neg x) + a.eval z x) + -(a.eval z x) :=
      (add_assoc _ _ _).symm
    _ = 0 + -(a.eval z x) := by rw [hz]
    _ = -(a.eval z x) := zero_add _

/-- Our own left subtraction lemma. -/
theorem sub_left (a : BilinearForm E) (x y z : V) :
    a.eval (E.sub x y) z = a.eval x z - a.eval y z := by
  change a.eval (E.add x (E.neg y)) z = a.eval x z - a.eval y z
  calc
    a.eval (E.add x (E.neg y)) z = a.eval x z + a.eval (E.neg y) z :=
      a.add_left x (E.neg y) z
    _ = a.eval x z + -(a.eval y z) := by rw [a.neg_left y z]
    _ = a.eval x z - a.eval y z := (sub_eq_add_neg _ _).symm

/-- Our own right subtraction lemma. -/
theorem sub_right (a : BilinearForm E) (z x y : V) :
    a.eval z (E.sub x y) = a.eval z x - a.eval z y := by
  change a.eval z (E.add x (E.neg y)) = a.eval z x - a.eval z y
  calc
    a.eval z (E.add x (E.neg y)) = a.eval z x + a.eval z (E.neg y) :=
      a.add_right z x (E.neg y)
    _ = a.eval z x + -(a.eval z y) := by rw [a.neg_right y z]
    _ = a.eval z x - a.eval z y := (sub_eq_add_neg _ _).symm

end BilinearForm
end Cea
