import CeaLemma.Foundation.Real

/-!
# Small proofs about the permitted real-number foundation

These are explicit derivations rather than calls to automated tactics such as
`ring`, `linarith`, `nlinarith`, `positivity`, or `aesop`.
-/

namespace Cea.RealInequalities

/-- Derive positivity of the square from multiplication of nonnegative reals. -/
theorem square_nonneg (x : ℝ) : 0 ≤ x ^ 2 := by
  by_cases hx : 0 ≤ x
  · calc
      0 ≤ x * x := mul_nonneg hx hx
      _ = x ^ 2 := (pow_two x).symm
  · have hnx : 0 ≤ -x := neg_nonneg.mpr (le_of_lt (lt_of_not_ge hx))
    calc
      0 ≤ (-x) * (-x) := mul_nonneg hnx hnx
      _ = x * x := neg_mul_neg x x
      _ = x ^ 2 := (pow_two x).symm

/-- Prove x ≤ |x| rather than calling Mathlib `le_abs_self`. -/
theorem self_le_abs (x : ℝ) : x ≤ |x| := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
  · have hn : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    rw [abs_of_nonpos hn]
    exact le_trans hn (neg_nonneg.mpr hn)

/-- Cancellation of a positive real factor, via a contradiction. -/
theorem cancel_pos_left {x y z : ℝ}
    (h : x * y ≤ x * z) (hx : 0 < x) : y ≤ z := by
  by_contra hn
  have hzy : z < y := lt_of_not_ge hn
  have hstrict : x * z < x * y := mul_lt_mul_of_pos_left hzy hx
  exact (not_lt_of_ge h) hstrict

/-- Positive denominators and nonnegative numerators. -/
theorem nonneg_div {x d : ℝ} (hx : 0 ≤ x) (hd : 0 < d) : 0 ≤ x / d := by
  rw [div_eq_mul_inv]
  exact mul_nonneg hx (le_of_lt (inv_pos.mpr hd))

/-- Strict positivity of a quotient. -/
theorem positive_div {x d : ℝ} (hx : 0 < x) (hd : 0 < d) : 0 < x / d := by
  have hi : 0 < d⁻¹ := inv_pos.mpr hd
  have hm : 0 * d⁻¹ < x * d⁻¹ := mul_lt_mul_of_pos_right hx hi
  calc
    (0 : ℝ) = 0 * d⁻¹ := (zero_mul _).symm
    _ < x * d⁻¹ := hm
    _ = x / d := (div_eq_mul_inv _ _).symm

/-- Multiplying by a positive denominator cancels division. -/
theorem div_mul_cancel_pos (x d : ℝ) (hd : 0 < d) :
    (x / d) * d = x := by
  calc
    (x / d) * d = (x * d⁻¹) * d := by rw [div_eq_mul_inv]
    _ = x * (d⁻¹ * d) := mul_assoc x d⁻¹ d
    _ = x * 1 := by rw [inv_mul_cancel₀ (ne_of_gt hd)]
    _ = x := mul_one x

/-- The corresponding cancellation in the other order. -/
theorem mul_div_cancel_pos (x d : ℝ) (hd : 0 < d) :
    (x * d) / d = x := by
  calc
    (x * d) / d = (x * d) * d⁻¹ := by rw [div_eq_mul_inv]
    _ = x * (d * d⁻¹) := mul_assoc x d d⁻¹
    _ = x * 1 := by rw [mul_inv_cancel₀ (ne_of_gt hd)]
    _ = x := mul_one x

/-- Derive division bound without using `le_div_iff₀`. -/
theorem le_div_of_mul_le {x y d : ℝ}
    (hd : 0 < d) (h : x * d ≤ y) : x ≤ y / d := by
  have hm : (x * d) * d⁻¹ ≤ y * d⁻¹ :=
    mul_le_mul_of_nonneg_right h (le_of_lt (inv_pos.mpr hd))
  calc
    x = (x * d) / d := (mul_div_cancel_pos x d hd).symm
    _ = (x * d) * d⁻¹ := div_eq_mul_inv _ _
    _ ≤ y * d⁻¹ := hm
    _ = y / d := (div_eq_mul_inv _ _).symm

/-- Derive another division bound without using `div_le_iff₀`. -/
theorem div_le_of_le_mul {x y d : ℝ}
    (hd : 0 < d) (h : x ≤ d * y) : x / d ≤ y := by
  have hm : x * d⁻¹ ≤ (d * y) * d⁻¹ :=
    mul_le_mul_of_nonneg_right h (le_of_lt (inv_pos.mpr hd))
  calc
    x / d = x * d⁻¹ := div_eq_mul_inv _ _
    _ ≤ (d * y) * d⁻¹ := hm
    _ = (y * d) * d⁻¹ := by rw [mul_comm d y]
    _ = (y * d) / d := (div_eq_mul_inv _ _).symm
    _ = y := mul_div_cancel_pos y d hd

/-- Multiply back a positive denominator, no `div_le_iff₀`. -/
theorem le_mul_of_div_le {x y d : ℝ}
    (hd : 0 < d) (h : x / d ≤ y) : x ≤ d * y := by
  have hm : (x / d) * d ≤ y * d :=
    mul_le_mul_of_nonneg_right h (le_of_lt hd)
  calc
    x = (x / d) * d := (div_mul_cancel_pos x d hd).symm
    _ ≤ y * d := hm
    _ = d * y := mul_comm y d

/-- Reshuffle an elementary product without `ring`. -/
theorem mul_square_swap (x a : ℝ) : x * (a * x) = a * x ^ 2 := by
  calc
    x * (a * x) = (x * a) * x := (mul_assoc x a x).symm
    _ = (a * x) * x := by rw [mul_comm x a]
    _ = a * (x * x) := mul_assoc a x x
    _ = a * x ^ 2 := by rw [pow_two]

/-- Three-factor reorder without `ring`. -/
theorem mul_triple_swap (a x y : ℝ) : (a * x) * y = x * (a * y) := by
  calc
    (a * x) * y = (x * a) * y := by rw [mul_comm a x]
    _ = x * (a * y) := mul_assoc x a y

/-- Division and multiplication reassociation without `ring`. -/
theorem div_mul_swap (m x d : ℝ) : (m * x) / d = (m / d) * x := by
  calc
    (m * x) / d = (m * x) * d⁻¹ := div_eq_mul_inv _ _
    _ = m * (x * d⁻¹) := mul_assoc m x d⁻¹
    _ = m * (d⁻¹ * x) := by rw [mul_comm x (d⁻¹)]
    _ = (m * d⁻¹) * x := (mul_assoc m d⁻¹ x).symm
    _ = (m / d) * x := by rw [div_eq_mul_inv]

end Cea.RealInequalities
