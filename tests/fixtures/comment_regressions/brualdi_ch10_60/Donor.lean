import Mathlib

structure LatinSquare (n : ℕ) where
  carrier : Matrix (Fin n) (Fin n) (ZMod n)
  pairwise_1 : ∀ i j1 j2, j1 ≠ j2 → carrier i j1 ≠ carrier i j2
  pairwise_2 : ∀ j i1 i2, i1 ≠ i2 → carrier i1 j ≠ carrier i2 j


def offDiagonalOccurrences {n : ℕ} (L : LatinSquare n) (a : ZMod n) :
    Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p =>
    p.1 ≠ p.2 ∧ L.carrier p.1 p.2 = a

-- This count isolates the Latin-square and diagonal part of the argument:
-- each symbol occurs once in every row, and idempotence removes its diagonal occurrence.


-- Symmetry pairs the off-diagonal occurrences of a symbol by swapping the two indices,
-- giving the parity fact needed to turn the preceding count into oddness of the order.
theorem offDiagonalOccurrences_card_even {n : ℕ} (L : LatinSquare n)
    (hSymm : L.carrier.IsSymm) (a : ZMod n) :
    Even (offDiagonalOccurrences L a).card := by
  classical
  let S := offDiagonalOccurrences L a
  let U := S.filter fun p => p.1 < p.2
  let V := S.filter fun p => ¬ p.1 < p.2
  have hswap (p : Fin n × Fin n) : p ∈ S ↔ p.swap ∈ S := by
    simp only [S, offDiagonalOccurrences, Finset.mem_filter, Finset.mem_univ,
      true_and, Prod.swap]
    constructor
    · rintro ⟨hne, heq⟩
      constructor
      · exact Ne.symm hne
      · rw [hSymm.apply p.1 p.2]
        exact heq
    · rintro ⟨hne, heq⟩
      constructor
      · exact Ne.symm hne
      · rw [hSymm.apply p.2 p.1]
        exact heq
  have huv : U.card = V.card := by
    apply Finset.card_bij (s := U) (t := V) (fun p _ => p.swap)
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpS, hlt⟩
      refine Finset.mem_filter.mpr ⟨(hswap p).mp hpS, ?_⟩
      simpa [Prod.swap] using (not_lt.mpr hlt.le)
    · intro p hp q hq heq
      have h := congrArg Prod.swap heq
      simpa using h
    · intro q hq
      rcases Finset.mem_filter.mp hq with ⟨hqS, hnlt⟩
      have hne : q.1 ≠ q.2 :=
        (Finset.mem_filter.mp hqS).2.1
      have hlt : q.2 < q.1 := by
        rcases lt_or_gt_of_ne hne with h | h
        · exact (hnlt h).elim
        · exact h
      refine ⟨q.swap, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨(hswap q).mp hqS, ?_⟩
        simpa [Prod.swap] using hlt
      · simp [Prod.swap]
  have hpart :
      U.card + V.card = S.card :=
    Finset.filter_card_add_filter_neg_card_eq_card (s := S)
      (p := fun p => p.1 < p.2)
  rw [huv.symm] at hpart
  rw [← hpart]
  exact Even.add_self U.card
