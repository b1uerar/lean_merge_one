import Mathlib
section

section


section


def clean (S : Set ℕ+) (n : ℕ) : Prop :=
  ∃! (S' : Finset ℕ+),
    ((S' : Set _) ⊆ S) ∧ (Odd S'.card) ∧ (∑ s ∈ S', (s : ℕ) = n)


end


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Distinct odd subfinsets of F have distinct positive sums at most the total;
-- this strict counting bound supplies gaps for finite blocks of S.

end


end

section


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Adjoining one fresh element turns equal even-cardinality subset sums into
-- equal odd-cardinality sums, giving uniqueness for the even subset sums too.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Adjoining one fresh element turns equal even-cardinality subset sums into
-- equal odd-cardinality sums, giving uniqueness for the even subset sums too.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Distinct odd subfinsets of F have distinct positive sums at most the total;
-- this strict counting bound supplies gaps for finite blocks of S.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Adjoining one fresh element turns equal even-cardinality subset sums into
-- equal odd-cardinality sums, giving uniqueness for the even subset sums too.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.


-- Unbounded gaps after finite initial blocks immediately give unclean
-- integers, since their total plus one has no subset-sum representation.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Adjoining one fresh element turns equal even-cardinality subset sums into
-- equal odd-cardinality sums, giving uniqueness for the even subset sums too.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Distinct odd subfinsets of F have distinct positive sums at most the total;
-- this strict counting bound supplies gaps for finite blocks of S.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Adjoining one fresh element turns equal even-cardinality subset sums into
-- equal odd-cardinality sums, giving uniqueness for the even subset sums too.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Adjoining one fresh element turns equal even-cardinality subset sums into
-- equal odd-cardinality sums, giving uniqueness for the even subset sums too.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Distinct odd subfinsets of F have distinct positive sums at most the total;
-- this strict counting bound supplies gaps for finite blocks of S.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Adjoining one fresh element turns equal even-cardinality subset sums into
-- equal odd-cardinality sums, giving uniqueness for the even subset sums too.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.


-- Unbounded gaps after finite initial blocks immediately give unclean
-- integers, since their total plus one has no subset-sum representation.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Adjoining one fresh element turns equal even-cardinality subset sums into
-- equal odd-cardinality sums, giving uniqueness for the even subset sums too.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Distinct odd subfinsets of F have distinct positive sums at most the total;
-- this strict counting bound supplies gaps for finite blocks of S.

-- If every integer in an interval below the next omitted element is clean,
-- its distinct odd representations must inject into the odd subfinsets of
-- the finite initial block whose sums lie below that cutoff.

-- Above the total of an initial block plus its next two elements, a
-- representation below the following cutoff must use both new elements;
-- removing them leaves an odd subset sum from the initial block.
theorem clean_interval_forces_two_large_elements
    (S : Set ℕ+) (F : Finset ℕ+) (x y z : ℕ+) (N : ℕ)
    (hF : (F : Set ℕ+) ⊆ S)
    (hxS : x ∈ S) (hyS : y ∈ S)
    (hxF : x ∉ F) (hyF : y ∉ F) (hxy : x < y)
    (hcut : ∀ s : ℕ+, s ∈ S →
      s ∉ insert x (insert y F) → z ≤ s)
    (hclean : ∀ m : ℕ, N < m → m < (z : ℕ) → clean S m) :
    ∀ m : ℕ, N < m →
      (∑ s ∈ F, (s : ℕ)) + (y : ℕ) < m →
      m < (z : ℕ) →
      ∃ C : Finset ℕ+, C ⊆ F ∧ (C : Set ℕ+) ⊆ S ∧ Odd C.card ∧
        (x : ℕ) + (y : ℕ) + ∑ s ∈ C, (s : ℕ) = m := by
  intro m hmN hlarge hmz
  obtain ⟨B, hB, _⟩ := hclean m hmN hmz
  have hsum : (∑ s ∈ B, (s : ℕ)) = m := hB.2.2
  have hBcut : B ⊆ insert x (insert y F) := by
    intro s hs
    by_contra hnot
    have hzs : (z : ℕ) ≤ (s : ℕ) :=
      hcut s (hB.1 hs) hnot
    have hsle : (s : ℕ) ≤ ∑ t ∈ B, (t : ℕ) :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hs
    omega
  have hxB : x ∈ B := by
    by_contra hxB
    have hsub : B ⊆ insert y F := by
      intro s hs
      have hs' := hBcut hs
      simp only [Finset.mem_insert] at hs'
      rcases hs' with hsx | hs'
      · subst s
        exact False.elim (hxB hs)
      · simpa only [Finset.mem_insert] using hs'
    have hbound : (∑ s ∈ B, (s : ℕ)) ≤
        (y : ℕ) + ∑ s ∈ F, (s : ℕ) := by
      calc
        _ ≤ ∑ s ∈ insert y F, (s : ℕ) :=
          Finset.sum_le_sum_of_subset hsub
        _ = (y : ℕ) + ∑ s ∈ F, (s : ℕ) := by simp [hyF]
    omega
  have hyB : y ∈ B := by
    by_contra hyB
    have hsub : B ⊆ insert x F := by
      intro s hs
      have hs' := hBcut hs
      simp only [Finset.mem_insert] at hs'
      rcases hs' with hsx | hs'
      · subst s
        exact Finset.mem_insert_self x F
      ·
        rcases hs' with hsy | hsF
        · subst s
          exact False.elim (hyB hs)
        · exact Finset.mem_insert_of_mem hsF
    have hbound : (∑ s ∈ B, (s : ℕ)) ≤
        (x : ℕ) + ∑ s ∈ F, (s : ℕ) := by
      calc
        _ ≤ ∑ s ∈ insert x F, (s : ℕ) :=
          Finset.sum_le_sum_of_subset hsub
        _ = (x : ℕ) + ∑ s ∈ F, (s : ℕ) := by simp [hxF]
    have hxyNat : (x : ℕ) < (y : ℕ) := by exact_mod_cast hxy
    omega
  let C : Finset ℕ+ := (B.erase x).erase y
  have hyNeX : y ≠ x := ne_of_gt hxy
  have hyErase : y ∈ B.erase x :=
    Finset.mem_erase.mpr ⟨hyNeX, hyB⟩
  have hCsub : C ⊆ F := by
    intro s hs
    have hs' : s ∈ (B.erase x).erase y := hs
    rcases Finset.mem_erase.mp hs' with ⟨hsy, hs'⟩
    rcases Finset.mem_erase.mp hs' with ⟨hsx, hsB⟩
    have hsIns := hBcut hsB
    simp only [Finset.mem_insert] at hsIns
    rcases hsIns with hseq | hsIns
    · subst s
      exact False.elim (hsx rfl)
    · rcases hsIns with hseq | hsF
      · subst s
        exact False.elim (hsy rfl)
      · exact hsF
  have hCS : (C : Set ℕ+) ⊆ S := fun s hs => hF (hCsub hs)
  have hrec : B = insert x (insert y C) := by
    change B = insert x (insert y ((B.erase x).erase y))
    calc
      B = insert x (B.erase x) := (Finset.insert_erase hxB).symm
      _ = insert x (insert y ((B.erase x).erase y)) := by
        rw [Finset.insert_erase hyErase]
  have hcard : B.card = C.card + 2 := by
    have h1 := Finset.card_erase_add_one hxB
    have h2 := Finset.card_erase_add_one hyErase
    dsimp [C]
    omega
  have hodd : Odd C.card := by
    have ho : Odd (C.card + 2) := by simpa [hcard] using hB.2.1
    have he : Even (2 : ℕ) := by norm_num
    have hsub := Nat.Odd.sub_even (by omega : 2 ≤ C.card + 2) ho he
    simpa using hsub
  have hsumrec : (∑ s ∈ B, (s : ℕ)) =
      (x : ℕ) + (y : ℕ) + ∑ s ∈ C, (s : ℕ) := by
    rw [hrec]
    simp [C, hxy.ne, add_assoc]
  exact ⟨C, hCsub, hCS, hodd, hsumrec.symm.trans hsum⟩


end


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Distinct odd subfinsets of F have distinct positive sums at most the total;
-- this strict counting bound supplies gaps for finite blocks of S.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Adjoining one fresh element turns equal even-cardinality subset sums into
-- equal odd-cardinality sums, giving uniqueness for the even subset sums too.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Adjoining one fresh element turns equal even-cardinality subset sums into
-- equal odd-cardinality sums, giving uniqueness for the even subset sums too.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Distinct odd subfinsets of F have distinct positive sums at most the total;
-- this strict counting bound supplies gaps for finite blocks of S.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Adjoining one fresh element turns equal even-cardinality subset sums into
-- equal odd-cardinality sums, giving uniqueness for the even subset sums too.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.


-- Unbounded gaps after finite initial blocks immediately give unclean
-- integers, since their total plus one has no subset-sum representation.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Adjoining one fresh element turns equal even-cardinality subset sums into
-- equal odd-cardinality sums, giving uniqueness for the even subset sums too.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Distinct odd subfinsets of F have distinct positive sums at most the total;
-- this strict counting bound supplies gaps for finite blocks of S.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Adjoining one fresh element turns equal even-cardinality subset sums into
-- equal odd-cardinality sums, giving uniqueness for the even subset sums too.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Adjoining one fresh element turns equal even-cardinality subset sums into
-- equal odd-cardinality sums, giving uniqueness for the even subset sums too.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Distinct odd subfinsets of F have distinct positive sums at most the total;
-- this strict counting bound supplies gaps for finite blocks of S.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Adjoining one fresh element turns equal even-cardinality subset sums into
-- equal odd-cardinality sums, giving uniqueness for the even subset sums too.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.


-- Unbounded gaps after finite initial blocks immediately give unclean
-- integers, since their total plus one has no subset-sum representation.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Adjoining one fresh element turns equal even-cardinality subset sums into
-- equal odd-cardinality sums, giving uniqueness for the even subset sums too.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Distinct odd subfinsets of F have distinct positive sums at most the total;
-- this strict counting bound supplies gaps for finite blocks of S.

-- If every integer in an interval below the next omitted element is clean,
-- its distinct odd representations must inject into the odd subfinsets of
-- the finite initial block whose sums lie below that cutoff.
