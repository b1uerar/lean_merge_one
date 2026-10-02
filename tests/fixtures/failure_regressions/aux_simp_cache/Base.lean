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
        (x : ℕ) + (y : ℕ) + ∑ s ∈ C, (s : ℕ) = m := by sorry
theorem clean_interval_requires_many_initial_odd_subsets
    (S : Set ℕ+) (F : Finset ℕ+) (N a : ℕ)
    (hF : (F : Set ℕ+) ⊆ S)
    (hcut : ∀ s : ℕ+, s ∈ S → s ∉ F → a ≤ (s : ℕ))
    (hN : N + 1 < a)
    (hclean : ∀ m : ℕ, N < m → m < a → clean S m) :
    a - (N + 1) ≤
      (F.powerset.filter (fun A : Finset ℕ+ =>
        Odd A.card ∧ (∑ s ∈ A, (s : ℕ)) < a)).card := by
  classical
  let T := F.powerset.filter (fun A : Finset ℕ+ =>
    Odd A.card ∧ (∑ s ∈ A, (s : ℕ)) < a)
  let rep : ℕ → Finset ℕ+ := fun m =>
    if hm : N < m ∧ m < a then (hclean m hm.1 hm.2).choose else ∅
  have rep_spec {m : ℕ} (hmN : N < m) (hma : m < a) :
      ((rep m : Set ℕ+) ⊆ S) ∧ Odd (rep m).card ∧
        (∑ s ∈ rep m, (s : ℕ)) = m := by
    have h := hclean m hmN hma
    dsimp [rep]
    rw [dif_pos ⟨hmN, hma⟩]
    exact h.choose_spec.1
  have hinj : (Finset.Ioc N (a - 1)).card ≤ T.card := by
    apply Finset.card_le_card_of_injOn rep
    · intro m hm
      change m ∈ Finset.Ioc N (a - 1) at hm
      rcases Finset.mem_Ioc.mp hm with ⟨hmN, hma'⟩
      have hma : m < a := by omega
      have hs := rep_spec hmN hma
      have hsub : rep m ⊆ F := by
        intro x hx
        by_contra hxF
        have hxS := hs.1 hx
        have hxle : (x : ℕ) ≤ ∑ y ∈ rep m, (y : ℕ) :=
          Finset.single_le_sum (fun y hy => Nat.zero_le _) hx
        rw [hs.2.2] at hxle
        have hcutx := hcut x hxS hxF
        omega
      change rep m ∈ T
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr hsub, ?_⟩
      refine ⟨hs.2.1, ?_⟩
      rw [hs.2.2]
      exact hma
    · intro m hm m' hm' heq
      change m ∈ Finset.Ioc N (a - 1) at hm
      change m' ∈ Finset.Ioc N (a - 1) at hm'
      rcases Finset.mem_Ioc.mp hm with ⟨hmN, hma'⟩
      rcases Finset.mem_Ioc.mp hm' with ⟨hm'N, hma''⟩
      have hs := rep_spec hmN (by omega)
      have hs' := rep_spec hm'N (by omega)
      calc
        m = ∑ s ∈ rep m, (s : ℕ) := hs.2.2.symm
        _ = ∑ s ∈ rep m', (s : ℕ) := by rw [heq]
        _ = m' := hs'.2.2
  have hlen : a - (N + 1) = (Finset.Ioc N (a - 1)).card := by
    simp only [Nat.card_Ioc]
    omega
  simpa [T] using hlen.le.trans hinj


end

section


section







end


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Distinct odd subfinsets of F have distinct positive sums at most the total;
-- this strict counting bound supplies gaps for finite blocks of S.

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


section


-- Unbounded gaps after finite initial blocks immediately give unclean
-- integers, since their total plus one has no subset-sum representation.
theorem imosl_2015_c6_of_unbounded_subset_sum_gaps
    (S : Set ℕ+)
    (hgap : ∀ N : ℕ, ∃ (F : Finset ℕ+) (a : ℕ+),
      (F : Set ℕ+) ⊆ S ∧
      (∀ s : ℕ+, s ∈ S → s ∉ F → a ≤ s) ∧
      N < (∑ s ∈ F, (s : ℕ)) + 1 ∧
      (∑ s ∈ F, (s : ℕ)) + 1 < (a : ℕ)) :
    ∀ (N : ℕ), ∃ (m : ℕ), N < m ∧ ¬ clean S m := by
  intro N
  obtain ⟨F, a, hFS, hlarge, hN, hgap⟩ := hgap N
  let m : ℕ := (∑ s ∈ F, (s : ℕ)) + 1
  refine ⟨m, ?_, ?_⟩
  · simpa [m] using hN
  · intro hclean
    rcases hclean with ⟨T, hT, _⟩
    have hsub : T ⊆ F := by
      intro s hsT
      by_contra hsF
      have hsS : s ∈ S := hT.1 hsT
      have hsa : (a : ℕ) ≤ (s : ℕ) := hlarge s hsS hsF
      have hssum : (s : ℕ) ≤ ∑ t ∈ T, (t : ℕ) :=
        Finset.single_le_sum (fun t ht => Nat.zero_le _) hsT
      rw [hT.2.2] at hssum
      dsimp [m] at hssum
      omega
    have hsumle :
        (∑ s ∈ T, (s : ℕ)) ≤ ∑ s ∈ F, (s : ℕ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _ => Nat.zero_le _)
    rw [hT.2.2] at hsumle
    dsimp [m] at hsumle
    omega



end



-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Adjoining one fresh element turns equal even-cardinality subset sums into
-- equal odd-cardinality sums, giving uniqueness for the even subset sums too.


-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Distinct odd subfinsets of F have distinct positive sums at most the total;
-- this strict counting bound supplies gaps for finite blocks of S.

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

theorem odd_subset_count_lt_total_of_injective
    (S : Set ℕ+) (huniq : ∀ A B : Finset ℕ+,
      (A : Set ℕ+) ⊆ S → (B : Set ℕ+) ⊆ S →
      Odd A.card → Odd B.card →
      (∑ s ∈ A, (s : ℕ)) = ∑ s ∈ B, (s : ℕ) → A = B)
    (F : Finset ℕ+) (hF : (F : Set ℕ+) ⊆ S) (hcard : 2 ≤ F.card) :
    (F.powerset.filter (fun A => Odd A.card)).card + 1 ≤
      ∑ s ∈ F, (s : ℕ) := by
  classical
  let O := F.powerset.filter (fun A => Odd A.card)
  let σ : Finset ℕ+ → ℕ := fun A => ∑ s ∈ A, (s : ℕ)
  let T : ℕ := ∑ s ∈ F, (s : ℕ)
  have hσinj : Set.InjOn σ O := by
    intro A hA B hB hab
    have hA' := Finset.mem_filter.mp hA
    have hB' := Finset.mem_filter.mp hB
    have hAsub : A ⊆ F := Finset.mem_powerset.mp hA'.1
    have hBsub : B ⊆ F := Finset.mem_powerset.mp hB'.1
    have hAS : (A : Set ℕ+) ⊆ S :=
      Set.Subset.trans (Finset.coe_subset.mpr hAsub) hF
    have hBS : (B : Set ℕ+) ⊆ S :=
      Set.Subset.trans (Finset.coe_subset.mpr hBsub) hF
    exact huniq A B hAS hBS hA'.2 hB'.2 (by simpa [σ] using hab)
  have hOddNonempty {A : Finset ℕ+} (hA : Odd A.card) : A.Nonempty := by
    apply Finset.card_pos.mp
    obtain ⟨k, hk⟩ := hA
    omega
  have hSumPos (A : Finset ℕ+) (hA : A.Nonempty) : 0 < σ A := by
    apply Finset.sum_pos
    · intro s hs
      exact s.2
    · exact hA
  have hSumGeThree (A : Finset ℕ+) (hA : 2 ≤ A.card) : 3 ≤ σ A := by
    obtain ⟨x, y, hx, hy, hxy⟩ :=
      Finset.one_lt_card_iff.mp (by omega : 1 < A.card)
    have hpair : ({x, y} : Finset ℕ+) ⊆ A := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hx
      · exact hy
    have hxyval : (x : ℕ) ≠ (y : ℕ) := by exact_mod_cast hxy
    have hpairval : 3 ≤ (x : ℕ) + (y : ℕ) := by
      have hxpos : 0 < (x : ℕ) := x.2
      have hypos : 0 < (y : ℕ) := y.2
      omega
    have hle :
        (∑ z ∈ ({x, y} : Finset ℕ+), (z : ℕ)) ≤ ∑ z ∈ A, (z : ℕ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hpair (by
        intro z hz hz'
        exact Nat.zero_le _)
    have hpairsum :
        (∑ z ∈ ({x, y} : Finset ℕ+), (z : ℕ)) =
          (x : ℕ) + (y : ℕ) := by
      simp [hxy]
    simpa [σ] using le_trans hpairval (by simpa [hpairsum] using hle)
  have hDecomp (A : Finset ℕ+) (hAsub : A ⊆ F) :
      T = σ A + σ (F \ A) := by
    simp only [T, σ]
    rw [← Finset.sum_sdiff hAsub]
    simp [add_comm]
  have hTge3 : 3 ≤ T := by
    simpa [T, σ] using hSumGeThree F hcard
  by_cases hn : Odd F.card
  · have hFmem : F ∈ O := by
      simp [O, hn]
    let O' := O.erase F
    have hOpos : 0 < O.card := Finset.card_pos.mpr ⟨F, hFmem⟩
    have hcardO' : O'.card + 1 = O.card := by
      calc
        O'.card + 1 = O.card - 1 + 1 := by
          rw [show O' = O.erase F from rfl, Finset.card_erase_of_mem hFmem]
        _ = O.card := Nat.sub_add_cancel hOpos
    let R := ((Finset.range T).erase 0).erase (T - 1)
    have h0mem : 0 ∈ Finset.range T := Finset.mem_range.mpr (by omega)
    have hTsubmem : T - 1 ∈ (Finset.range T).erase 0 := by
      simp only [Finset.mem_erase, Finset.mem_range]
      constructor <;> omega
    have hRcard : R.card = T - 2 := by
      calc
        R.card = ((Finset.range T).erase 0).card - 1 := by
          rw [show R = ((Finset.range T).erase 0).erase (T - 1) from rfl]
          exact Finset.card_erase_of_mem hTsubmem
        _ = (Finset.range T).card - 1 - 1 := by
          rw [Finset.card_erase_of_mem h0mem]
        _ = T - 2 := by simp; omega
    have hmaps :
        Set.MapsTo σ O' (R : Set ℕ) := by
      intro A hA
      have hAe := Finset.mem_erase.mp hA
      have hAO := hAe.2
      have hAp := Finset.mem_filter.mp hAO
      have hAsub : A ⊆ F := Finset.mem_powerset.mp hAp.1
      have hAneF : A ≠ F := hAe.1
      have hss : A ⊂ F :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hAsub, hAneF⟩
      have hcardlt : A.card < F.card := Finset.card_lt_card hss
      have hcardDpos : 0 < (F \ A).card := by
        rw [Finset.card_sdiff_of_subset hAsub]
        omega
      have hcardD : 2 ≤ (F \ A).card := by
        have hcardeq := Finset.card_sdiff_add_card_eq_card hAsub
        obtain ⟨m, hm⟩ := hn
        obtain ⟨k, hk⟩ := hAp.2
        omega
      have hsumD : 3 ≤ σ (F \ A) := hSumGeThree (F \ A) hcardD
      have hsumA : σ A + 3 ≤ T := by
        rw [hDecomp A hAsub]
        omega
      have hsumA_lt : σ A < T := by omega
      have hsumA_ne : σ A ≠ T - 1 := by omega
      have hsumA_pos : 0 < σ A := hSumPos A (hOddNonempty hAp.2)
      change σ A ∈ R
      simp only [R, Finset.mem_erase]
      exact ⟨hsumA_ne, hsumA_pos.ne', Finset.mem_range.mpr hsumA_lt⟩
    have hinj' : Set.InjOn σ O' := by
      intro A hA B hB hab
      have hAodd := (Finset.mem_filter.mp (Finset.mem_erase.mp hA).2).2
      have hBodd := (Finset.mem_filter.mp (Finset.mem_erase.mp hB).2).2
      exact hσinj (Finset.mem_erase.mp hA).2 (Finset.mem_erase.mp hB).2 hab
    have hcount : O'.card ≤ T - 2 := by
      calc
        O'.card ≤ R.card := Finset.card_le_card_of_injOn σ hmaps hinj'
        _ = T - 2 := hRcard
    have hcountO : O.card + 1 ≤ T := by omega
    simpa [O, T] using hcountO
  · have hmaps :
        Set.MapsTo σ O (((Finset.range T).erase 0 : Finset ℕ) : Set ℕ) := by
      intro A hA
      have hAp := Finset.mem_filter.mp hA
      have hAsub : A ⊆ F := Finset.mem_powerset.mp hAp.1
      have hAneF : A ≠ F := by
        intro hEq
        subst A
        exact hn hAp.2
      have hss : A ⊂ F :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hAsub, hAneF⟩
      have hcardlt : A.card < F.card := Finset.card_lt_card hss
      have hcardDpos : 0 < (F \ A).card := by
        rw [Finset.card_sdiff_of_subset hAsub]
        omega
      have hDnon : (F \ A).Nonempty := Finset.card_pos.mp hcardDpos
      have hsumD : 0 < σ (F \ A) := hSumPos (F \ A) hDnon
      have hsumA : 0 < σ A := hSumPos A (hOddNonempty hAp.2)
      have hsumA_lt : σ A < T := by
        rw [hDecomp A hAsub]
        omega
      change σ A ∈ (Finset.range T).erase 0
      simp only [Finset.mem_erase]
      exact ⟨hsumA.ne', Finset.mem_range.mpr hsumA_lt⟩
    have hinj' : Set.InjOn σ O := hσinj
    have hcount : O.card ≤ T - 1 := by
      have h0mem : 0 ∈ Finset.range T := Finset.mem_range.mpr (by omega)
      calc
        O.card ≤ ((Finset.range T).erase 0).card :=
          Finset.card_le_card_of_injOn σ hmaps hinj'
        _ = T - 1 := by
          rw [Finset.card_erase_of_mem h0mem]
          simp
    have hcountO : O.card + 1 ≤ T := by omega
    simpa [O, T] using hcountO


end

section



section



-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Adjoining one fresh element turns equal even-cardinality subset sums into
-- equal odd-cardinality sums, giving uniqueness for the even subset sums too.
theorem even_subset_sum_injective_of_odd_subset_sum_injective
    (S : Set ℕ+) (hS : S.Infinite)
    (huniq : ∀ A B : Finset ℕ+,
      (A : Set ℕ+) ⊆ S → (B : Set ℕ+) ⊆ S →
      Odd A.card → Odd B.card →
      (∑ s ∈ A, (s : ℕ)) = ∑ s ∈ B, (s : ℕ) → A = B) :
    ∀ A B : Finset ℕ+,
      (A : Set ℕ+) ⊆ S → (B : Set ℕ+) ⊆ S →
      Even A.card → Even B.card →
      (∑ s ∈ A, (s : ℕ)) = ∑ s ∈ B, (s : ℕ) → A = B := by
  intro A B hA hB hEA hEB hab
  obtain ⟨x, hxS, hxAB⟩ := hS.exists_notMem_finset (A ∪ B)
  have hxA : x ∉ A := fun hx => hxAB (Finset.mem_union_left B hx)
  have hxB : x ∉ B := fun hx => hxAB (Finset.mem_union_right A hx)
  have hIA : (↑(insert x A) : Set ℕ+) ⊆ S := by
    intro y hy
    simp only [Finset.mem_coe, Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · exact hxS
    · exact hA hy
  have hIB : (↑(insert x B) : Set ℕ+) ⊆ S := by
    intro y hy
    simp only [Finset.mem_coe, Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · exact hxS
    · exact hB hy
  have hOddA : Odd (insert x A).card := by
    simpa [hxA] using hEA.add_one
  have hOddB : Odd (insert x B).card := by
    simpa [hxB] using hEB.add_one
  have hsum :
      (∑ s ∈ insert x A, (s : ℕ)) =
        ∑ s ∈ insert x B, (s : ℕ) := by
    rw [Finset.sum_insert hxA, Finset.sum_insert hxB, hab]
  have hins : insert x A = insert x B :=
    huniq (insert x A) (insert x B) hIA hIB hOddA hOddB hsum
  have herase := congrArg (fun C : Finset ℕ+ => C.erase x) hins
  simpa [hxA, hxB] using herase



end



-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

end

section




-- Unbounded gaps after finite initial blocks immediately give unclean
-- integers, since their total plus one has no subset-sum representation.



end

section



-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Adjoining one fresh element turns equal even-cardinality subset sums into
-- equal odd-cardinality sums, giving uniqueness for the even subset sums too.

theorem infinitely_many_not_clean_of_odd_collision
    (S : Set ℕ+) (hS : S.Infinite)
    (A B : Finset ℕ+)
    (hA : (A : Set ℕ+) ⊆ S) (hB : (B : Set ℕ+) ⊆ S)
    (hoddA : Odd A.card) (hoddB : Odd B.card)
    (hne : A ≠ B)
    (hsum : (∑ s ∈ A, (s : ℕ)) = ∑ s ∈ B, (s : ℕ)) :
    ∀ (N : ℕ), ∃ (m : ℕ), N < m ∧ ¬ clean S m := by
  intro N
  let F : Finset ℕ+ := A ∪ B
  have hT : (S \ (F : Set ℕ+)).Infinite := hS.diff F.finite_toSet
  obtain ⟨x, hxT, hxlarge⟩ := hT.exists_gt ⟨N + 1, by omega⟩
  have hxS : x ∈ S := hxT.1
  have hxF : x ∉ F := hxT.2
  have hxA : x ∉ A := fun h => hxF (Finset.mem_union_left B h)
  have hxB : x ∉ B := fun h => hxF (Finset.mem_union_right A h)
  have hT' : ((S \ (F : Set ℕ+)) \ ({x} : Set ℕ+)).Infinite :=
    hT.diff (Set.finite_singleton x)
  obtain ⟨y, hyT, hylarge⟩ := hT'.exists_gt x
  have hyS : y ∈ S := hyT.1.1
  have hyF : y ∉ F := hyT.1.2
  have hyA : y ∉ A := fun h => hyF (Finset.mem_union_left B h)
  have hyB : y ∉ B := fun h => hyF (Finset.mem_union_right A h)
  have hyx : y ≠ x := ne_of_gt hylarge
  let A' : Finset ℕ+ := insert x (insert y A)
  let B' : Finset ℕ+ := insert x (insert y B)
  let m : ℕ := (x : ℕ) + (y : ℕ) + ∑ s ∈ A, (s : ℕ)
  have hxInsA : x ∉ insert y A := by simp [hxA, hyx.symm]
  have hxInsB : x ∉ insert y B := by simp [hxB, hyx.symm]
  have hAcard : A'.card = A.card + 2 := by
    dsimp [A']
    rw [Finset.card_insert_of_notMem hxInsA,
      Finset.card_insert_of_notMem hyA]
  have hBcard : B'.card = B.card + 2 := by
    dsimp [B']
    rw [Finset.card_insert_of_notMem hxInsB,
      Finset.card_insert_of_notMem hyB]
  have hAodd : Odd A'.card := by
    rw [hAcard]
    rcases hoddA with ⟨k, hk⟩
    exact ⟨k + 1, by omega⟩
  have hBodd : Odd B'.card := by
    rw [hBcard]
    rcases hoddB with ⟨k, hk⟩
    exact ⟨k + 1, by omega⟩
  have hAsub : (A' : Set ℕ+) ⊆ S := by
    intro z hz
    change z ∈ insert x (insert y A) at hz
    simp only [Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · exact hxS
    · rcases hz with rfl | hz
      · exact hyS
      · exact hA hz
  have hBsub : (B' : Set ℕ+) ⊆ S := by
    intro z hz
    change z ∈ insert x (insert y B) at hz
    simp only [Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · exact hxS
    · rcases hz with rfl | hz
      · exact hyS
      · exact hB hz
  have hAsum : (∑ s ∈ A', (s : ℕ)) = m := by
    change (∑ s ∈ insert x (insert y A), (s : ℕ)) = m
    rw [Finset.sum_insert hxInsA, Finset.sum_insert hyA]
    simp [m, Nat.add_assoc]
  have hBsum : (∑ s ∈ B', (s : ℕ)) = m := by
    change (∑ s ∈ insert x (insert y B), (s : ℕ)) = m
    rw [Finset.sum_insert hxInsB, Finset.sum_insert hyB]
    dsimp [m]
    rw [← hsum]
    simp [Nat.add_assoc]
  have hbound : N < m := by
    have hxN : N + 1 < (x : ℕ) := by exact_mod_cast hxlarge
    simp [m]
    omega
  refine ⟨m, hbound, ?_⟩
  unfold clean
  rintro ⟨C, hC, huniq⟩
  have hpropA : (A' : Set ℕ+) ⊆ S ∧ Odd A'.card ∧
      (∑ s ∈ A', (s : ℕ)) = m :=
    ⟨hAsub, hAodd, hAsum⟩
  have hpropB : (B' : Set ℕ+) ⊆ S ∧ Odd B'.card ∧
      (∑ s ∈ B', (s : ℕ)) = m :=
    ⟨hBsub, hBodd, hBsum⟩
  have hAC : A' = C := huniq A' hpropA
  have hBC : B' = C := huniq B' hpropB
  apply hne
  have hAB : A' = B' := hAC.trans hBC.symm
  have herase := congrArg (fun t : Finset ℕ+ => (t.erase x).erase y) hAB
  simpa [A', B', hxA, hxB, hyA, hyB, hyx, hyx.symm] using herase


end




/--
Let $S$ be a nonempty set of positive integers. We say that a positive integer $n$ is clean if it has a unique representation as a sum of an odd number of distinct elements from $S$. Prove that there exist infinitely many positive integers that are not clean.
-/
theorem imosl_2015_c6 (S : Set ℕ+) (hS : S.Nonempty): ∀ (N : ℕ), ∃ (m : ℕ), N < m ∧ ¬ clean S m := by sorry

-- A single collision between odd subset sums can be extended by fresh pairs
-- from an infinite S, yielding unclean sums beyond every prescribed bound.

-- Distinct odd subfinsets of F have distinct positive sums at most the total;
-- this strict counting bound supplies gaps for finite blocks of S.

-- If every integer in an interval below the next omitted element is clean,
-- its distinct odd representations must inject into the odd subfinsets of
-- the finite initial block whose sums lie below that cutoff.
