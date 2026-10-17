import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# The permitted Mathlib boundary

This module is the ONLY gateway to Mathlib.
We reuse the ordered complete field of real numbers, including `sInf`.
All vector spaces, norms, trial spaces, bilinear forms, and Galerkin / Cea
proofs are defined in this repository.
-/
