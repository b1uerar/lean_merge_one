import Mathlib
section

section



structure LatinSquare (n : ℕ) where
  carrier : Matrix (Fin n) (Fin n) (ZMod n)
  pairwise_1 : ∀ i j1 j2, j1 ≠ j2 → carrier i j1 ≠ carrier i j2
  pairwise_2 : ∀ j i1 i2, i1 ≠ i2 → carrier i1 j ≠ carrier i2 j



def offDiagonalOccurrences {n : ℕ} (L : LatinSquare n) (a : ZMod n) :
    Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p =>
    p.1 ≠ p.2 ∧ L.carrier p.1 p.2 = a



end


end

section


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


end

section





def IsIdempotent {n : ℕ} (L : LatinSquare n) : Prop :=
  ∀ i, L.carrier i i = i





end

section


-- This count isolates the Latin-square and diagonal part of the argument:
-- each symbol occurs once in every row, and idempotence removes its diagonal occurrence.
theorem offDiagonalOccurrences_card {n : ℕ} (L : LatinSquare n)
    (hIdem : IsIdempotent L) (a : ZMod n) :
    (offDiagonalOccurrences L a).card = n - 1 := by
  classical
  cases n with
  | zero =>
      simp [offDiagonalOccurrences]
  | succ n =>
      letI : NeZero (n + 1) := ⟨Nat.succ_ne_zero _⟩
      let k : Fin (n + 1) := (ZMod.finEquiv (n + 1)).symm a
      have hk : (k : ZMod (n + 1)) = a := by
        change k = a
        rfl
      have hcast (i : Fin (n + 1)) :
          ((i.val : ℕ) : ZMod (n + 1)) = a ↔ i = k := by
        constructor
        · intro hi
          have hi' := hi
          rw [Fin.cast_val_eq_self] at hi'
          exact hi'.trans hk.symm
        · intro hi
          rw [Fin.cast_val_eq_self]
          exact hi.trans hk
      have rowBij (i : Fin (n + 1)) :
          Function.Bijective (fun j : Fin (n + 1) => L.carrier i j) := by
        rw [Fintype.bijective_iff_injective_and_card]
        constructor
        · intro j₁ j₂ h
          by_contra hne
          exact (L.pairwise_1 i j₁ j₂ hne) h
        · simp [ZMod.card]
      have rowExists (i : Fin (n + 1)) :
          ∃ j : Fin (n + 1), L.carrier i j = a := by
        obtain ⟨j, hj⟩ := (rowBij i).2 a
        exact ⟨j, hj⟩
      let Occ := {p : Fin (n + 1) × Fin (n + 1) //
        L.carrier p.1 p.2 = a}
      let f : Occ → Fin (n + 1) := fun p => p.1.1
      have hf : Function.Bijective f := by
        constructor
        · intro x y hxy
          apply Subtype.ext
          apply Prod.ext
          · exact hxy
          · by_contra hne
            have heq : L.carrier x.1.1 x.1.2 = L.carrier x.1.1 y.1.2 := by
              calc
                L.carrier x.1.1 x.1.2 = a := x.2
                _ = L.carrier y.1.1 y.1.2 := y.2.symm
                _ = L.carrier x.1.1 y.1.2 :=
                  congrArg (fun r => L.carrier r y.1.2) hxy.symm
            exact (L.pairwise_1 x.1.1 x.1.2 y.1.2 hne) heq
        · intro i
          obtain ⟨j, hj⟩ := rowExists i
          exact ⟨⟨(i, j), hj⟩, rfl⟩
      have hOccCard : Fintype.card Occ = n + 1 :=
        (Fintype.card_congr (Equiv.ofBijective f hf)).trans (Fintype.card_fin _)
      let S : Finset (Fin (n + 1) × Fin (n + 1)) :=
        Finset.univ.filter fun p => L.carrier p.1 p.2 = a
      let g : {p // p ∈ S} → Occ := fun p =>
        ⟨p.1, by
          simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using p.2⟩
      have hg : Function.Bijective g := by
        constructor
        · intro x y hxy
          apply Subtype.ext
          exact congrArg (fun z : Occ => z.1) hxy
        · intro x
          refine ⟨⟨x.1, ?_⟩, ?_⟩
          · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
            exact x.2
          · rfl
      have hSCard : S.card = n + 1 := by
        calc
          S.card = Fintype.card {p // p ∈ S} := (Fintype.card_coe S).symm
          _ = Fintype.card Occ := Fintype.card_congr (Equiv.ofBijective g hg)
          _ = n + 1 := hOccCard
      have hset : offDiagonalOccurrences L a = S.erase (k, k) := by
        ext p
        simp only [offDiagonalOccurrences, Finset.mem_filter, Finset.mem_univ,
          true_and, Finset.mem_erase, S]
        constructor
        · rintro ⟨hne, hval⟩
          constructor
          · intro heq
            apply hne
            exact (congrArg Prod.fst heq).trans (congrArg Prod.snd heq).symm
          · exact hval
        · rintro ⟨hne, hval⟩
          constructor
          · intro hdiag
            rcases p with ⟨i, j⟩
            change i = j at hdiag
            subst j
            change L.carrier i i = a at hval
            rw [hIdem i] at hval
            change ((i.val : ℕ) : ZMod (n + 1)) = a at hval
            have hik : i = k := (hcast i).mp hval
            apply hne
            subst i
            rfl
          · exact hval
      have hmem : (k, k) ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hIdem k, hk]
        exact Fin.cast_val_eq_self a
      calc
        (offDiagonalOccurrences L a).card = (S.erase (k, k)).card :=
          congrArg Finset.card hset
        _ = S.card - 1 := Finset.card_erase_of_mem hmem
        _ = n + 1 - 1 := by rw [hSCard]
        _ = Nat.succ n - 1 := by omega


-- Symmetry pairs the off-diagonal occurrences of a symbol by swapping the two indices,
-- giving the parity fact needed to turn the preceding count into oddness of the order.

end








-- This count isolates the Latin-square and diagonal part of the argument:
-- each symbol occurs once in every row, and idempotence removes its diagonal occurrence.


-- Symmetry pairs the off-diagonal occurrences of a symbol by swapping the two indices,
-- giving the parity fact needed to turn the preceding count into oddness of the order.


/--
Prove that a symmetric, idempotent Latin square has odd order.
-/
theorem brualdi_ch10_60 {n : ℕ} (hn : n > 0) (L : LatinSquare n) :
    IsIdempotent L ∧ L.1.IsSymm → Odd n := by sorry
