import Mathlib

structure LatinSquare (n : ℕ) where
  carrier : Matrix (Fin n) (Fin n) (ZMod n)
  pairwise_1 : ∀ i j1 j2, j1 ≠ j2 → carrier i j1 ≠ carrier i j2
  pairwise_2 : ∀ j i1 i2, i1 ≠ i2 → carrier i1 j ≠ carrier i2 j

def IsIdempotent {n : ℕ} (L : LatinSquare n) : Prop :=
  ∀ i, L.carrier i i = i

def offDiagonalOccurrences {n : ℕ} (L : LatinSquare n) (a : ZMod n) :
    Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p =>
    p.1 ≠ p.2 ∧ L.carrier p.1 p.2 = a

-- This count isolates the Latin-square and diagonal part of the argument:
-- each symbol occurs once in every row, and idempotence removes its diagonal occurrence.
theorem offDiagonalOccurrences_card {n : ℕ} (L : LatinSquare n)
    (hIdem : IsIdempotent L) (a : ZMod n) :
    (offDiagonalOccurrences L a).card = n - 1 := by
  sorry

-- Symmetry pairs the off-diagonal occurrences of a symbol by swapping the two indices,
-- giving the parity fact needed to turn the preceding count into oddness of the order.
theorem offDiagonalOccurrences_card_even {n : ℕ} (L : LatinSquare n)
    (hSymm : L.carrier.IsSymm) (a : ZMod n) :
    Even (offDiagonalOccurrences L a).card := by
  sorry

/--
Prove that a symmetric, idempotent Latin square has odd order.
-/
theorem brualdi_ch10_60 {n : ℕ} (hn : n > 0) (L : LatinSquare n) :
    IsIdempotent L ∧ L.1.IsSymm → Odd n := by sorry
