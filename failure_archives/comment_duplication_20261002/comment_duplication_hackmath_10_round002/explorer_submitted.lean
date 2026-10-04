import Mathlib


-- This counts the bounded allocation pairs by separating the two fruit
-- totals into independent weak-composition counts.
theorem fin3_pair_sum_count (a b : ℕ) :
    (Finset.univ.filter (fun f : Fin 3 → Fin (a + 1) × Fin (b + 1) =>
      (∑ i, (f i).1.val) = a ∧ (∑ i, (f i).2.val) = b)).card =
        Nat.choose (a + 2) 2 * Nat.choose (b + 2) 2 := by
  sorry

/--
How many different ways can three people divide seven pears and five apples?
-/
theorem hackmath_10 (sols : Finset (Fin 3 → (ℕ × ℕ)))
    (h_sols : ∀ f, f ∈ sols ↔ (∑ i, (f i).1 = 7 ∧ ∑ i, (f i).2 = 5)) :
    sols.card = ((756) : ℕ ) := by sorry
