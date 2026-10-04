import Mathlib

def clean (S : Set ℕ+) (n : ℕ) : Prop :=
  ∃! (S' : Finset ℕ+),
    ((S' : Set _) ⊆ S) ∧ (Odd S'.card) ∧ (∑ s ∈ S', (s : ℕ) = n)

-- In a contradiction argument where all sufficiently large integers are clean,
-- this lets us track the unique representation after exchanging one element.
theorem clean_swap_forced
    (S : Set ℕ+) (A : Finset ℕ+) (hAS : (A : Set ℕ+) ⊆ S)
    (hAodd : Odd A.card) (a : ℕ+) (ha : a ∈ A)
    (b : ℕ+) (hb : b ∈ S) (hbA : b ∉ A)
    (hm : clean S ((∑ s ∈ A.erase a, (s : ℕ)) + b)) :
    ∀ C : Finset ℕ+,
      (C : Set ℕ+) ⊆ S → Odd C.card →
      (∑ s ∈ C, (s : ℕ)) = (∑ s ∈ A.erase a, (s : ℕ)) + b →
      C = insert b (A.erase a) := by
  let B := insert b (A.erase a)
  have hbErase : b ∉ A.erase a := by
    intro h
    exact hbA (Finset.mem_of_mem_erase h)
  have hcardErase : (A.erase a).card + 1 = A.card :=
    Finset.card_erase_add_one ha
  have hcardB : B.card = A.card := by
    dsimp [B]
    rw [Finset.card_insert_of_notMem hbErase]
    omega
  have hBodd : Odd B.card := by
    simpa [hcardB] using hAodd
  have hBsub : (B : Set ℕ+) ⊆ S := by
    intro x hx
    change x ∈ insert b (A.erase a) at hx
    simp only [Finset.mem_insert] at hx
    rcases hx with hx | hx
    · simpa [hx] using hb
    · exact hAS (Finset.mem_of_mem_erase hx)
  have hBsum :
      (∑ s ∈ B, (s : ℕ)) = (∑ s ∈ A.erase a, (s : ℕ)) + b := by
    dsimp [B]
    rw [Finset.sum_insert hbErase]
    exact Nat.add_comm _ _
  rcases hm with ⟨D, ⟨hDsub, hDodd, hDsum⟩, hDuniq⟩
  intro C hCsub hCodd hCsum
  have hCD : C = D := hDuniq C ⟨hCsub, hCodd, hCsum⟩
  have hBD : B = D := hDuniq B ⟨hBsub, hBodd, hBsum⟩
  change C = B
  exact hCD.trans hBD.symm

-- This proves the finite-set case of the main theorem by bounding every
-- possible representation by the sum of all elements of S.
theorem not_clean_unbounded_of_finite (S : Set ℕ+) (hS : S.Finite) :
    ∀ N : ℕ, ∃ m : ℕ, N < m ∧ ¬ clean S m := by
  classical
  let F := hS.toFinset
  let B := ∑ s ∈ F, (s : ℕ)
  intro N
  refine ⟨N + B + 1, by omega, ?_⟩
  intro hm
  rcases hm with ⟨T, ⟨hTS, hTodd, hsum⟩, huniq⟩
  have hTF : T ⊆ F := by
    intro x hx
    have hxS : x ∈ S := hTS hx
    change x ∈ F
    simpa [F] using hxS
  have hbound : (∑ s ∈ T, (s : ℕ)) ≤ B := by
    dsimp [B]
    exact Finset.sum_le_sum_of_subset_of_nonneg hTF
      (by intro x hx hxnot; exact Nat.zero_le _)
  rw [hsum] at hbound
  omega

-- Appending an element outside both representations converts equal even
-- representations into odd ones, where eventual cleanliness forces equality.
theorem even_representations_eq_of_clean_tail
    (S : Set ℕ+) (hS : S.Infinite) (N m : ℕ)
    (hclean : ∀ n : ℕ, N < n → clean S n) (hm : N < m)
    (A B : Finset ℕ+) (hAS : (A : Set ℕ+) ⊆ S)
    (hBS : (B : Set ℕ+) ⊆ S) (hAeven : Even A.card) (hBeven : Even B.card)
    (hAsum : (∑ s ∈ A, (s : ℕ)) = m) (hBsum : (∑ s ∈ B, (s : ℕ)) = m) :
    A = B := by
  classical
  obtain ⟨c, hcS, hcAB⟩ : ∃ c ∈ S, c ∉ A ∪ B := by
    by_contra h
    push_neg at h
    have hsub : S ⊆ (A ∪ B : Finset ℕ+) := by
      intro x hx
      exact h x hx
    exact hS ((Set.toFinite (A ∪ B : Finset ℕ+)).subset hsub)
  have hcA : c ∉ A := fun h => hcAB (Finset.mem_union.mpr (Or.inl h))
  have hcB : c ∉ B := fun h => hcAB (Finset.mem_union.mpr (Or.inr h))
  have hAodd : Odd (insert c A).card := by
    rw [Finset.card_insert_of_notMem hcA]
    rcases hAeven with ⟨k, hk⟩
    rw [hk]
    exact ⟨k, by omega⟩
  have hBodd : Odd (insert c B).card := by
    rw [Finset.card_insert_of_notMem hcB]
    rcases hBeven with ⟨k, hk⟩
    rw [hk]
    exact ⟨k, by omega⟩
  have hA' : ((insert c A : Finset ℕ+) : Set ℕ+) ⊆ S := by
    intro x hx
    change x ∈ insert c A at hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hcS
    · exact hAS hx
  have hB' : ((insert c B : Finset ℕ+) : Set ℕ+) ⊆ S := by
    intro x hx
    change x ∈ insert c B at hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hcS
    · exact hBS hx
  have hA'sum : (∑ s ∈ insert c A, (s : ℕ)) = m + c := by
    rw [Finset.sum_insert hcA, hAsum]
    exact Nat.add_comm _ _
  have hB'sum : (∑ s ∈ insert c B, (s : ℕ)) = m + c := by
    rw [Finset.sum_insert hcB, hBsum]
    exact Nat.add_comm _ _
  rcases hclean (m + c) (by omega) with ⟨D, ⟨hDS, hDodd, hDsum⟩, hDuniq⟩
  have hAD : insert c A = D := hDuniq _ ⟨hA', hAodd, hA'sum⟩
  have hBD : insert c B = D := hDuniq _ ⟨hB', hBodd, hB'sum⟩
  apply Finset.ext
  intro x
  have hmem := congrArg (fun T : Finset ℕ+ => x ∈ T) (hAD.trans hBD.symm)
  by_cases hxc : x = c
  · subst x
    simp [hcA, hcB]
  · simpa [Finset.mem_insert, hxc] using hmem

-- Any representation of a clean number below a cutoff uses only elements
-- below that cutoff, which makes finite initial segments control such sums.
theorem clean_rep_below_cutoff
    (S : Set ℕ+) (n : ℕ) (t : ℕ+) (hnt : n < (t : ℕ))
    (hn : clean S n) :
    ∃ A : Finset ℕ+,
      (A : Set ℕ+) ⊆ S ∧ Odd A.card ∧
      (∑ s ∈ A, (s : ℕ)) = n ∧
      ∀ s ∈ A, (s : ℕ) < (t : ℕ) := by
  rcases hn with ⟨A, ⟨hAS, hAodd, hAsum⟩, hAuniq⟩
  refine ⟨A, hAS, hAodd, hAsum, ?_⟩
  intro s hs
  have hsle : (s : ℕ) ≤ ∑ x ∈ A, (x : ℕ) :=
    Finset.single_le_sum (s := A) (f := fun (x : ℕ+) => (x : ℕ)) (a := s)
      (fun x hx => Nat.zero_le _) hs
  rw [hAsum] at hsle
  exact lt_of_le_of_lt hsle hnt

-- If every integer past N is clean, the clean integers before a cutoff t
-- must all be supplied by odd subsets of F; counting those subsets bounds
-- how quickly the finite initial segment can grow.
theorem clean_tail_bounds_finite_cutoff
    (S : Set ℕ+) (N t : ℕ) (F : Finset ℕ+)
    (hclean : ∀ n : ℕ, N < n → clean S n)
    (hFsub : (F : Set ℕ+) ⊆ S)
    (hFcomplete : ∀ s ∈ S, (s : ℕ) < t → s ∈ F)
    (hFbelow : ∀ s ∈ F, (s : ℕ) < t) :
    t ≤ N + 2 ^ F.card + 1 := by
  sorry

/--
Let $S$ be a nonempty set of positive integers. We say that a positive integer $n$ is clean if it has a unique representation as a sum of an odd number of distinct elements from $S$. Prove that there exist infinitely many positive integers that are not clean.
-/
theorem imosl_2015_c6 (S : Set ℕ+) (hS : S.Nonempty): ∀ (N : ℕ), ∃ (m : ℕ), N < m ∧ ¬ clean S m := by
  classical
  intro N
  by_cases hSf : S.Finite
  · exact not_clean_unbounded_of_finite S hSf N
  · sorry
