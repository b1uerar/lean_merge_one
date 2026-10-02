import Mathlib
section


open scoped Finset


-- The condition of the problem. Following usual Lean conventions, this is expressed with indices starting from 0, rather than from 1 as in the informal statement (but `N` remains as the index of the last term for which `a n` is not defined in terms of previous terms).
def Condition (a : ℕ → ℕ) (N : ℕ) : Prop :=
  (∀ i, 0 < a i) ∧ ∀ n, N < n → a n = #{i ∈ Finset.range n | a i = a (n - 1)}


end


-- The property of a sequence being eventually periodic.


-- The condition of the problem. Following usual Lean conventions, this is expressed with indices starting from 0, rather than from 1 as in the informal statement (but `N` remains as the index of the last term for which `a n` is not defined in terms of previous terms).


-- The property of a sequence being eventually periodic.


section


open scoped Finset


/--
Counting self-duality of the recurrence: for every `m ≥ 1`, the value `m` occurs infinitely often
if and only if infinitely many values occur at least `m` times.

Why this helps. Unfolding the rule at an index `i > N` says that `a i` is the number of earlier
occurrences of the previous value `a (i-1)`, i.e. `a i = m` exactly when the position `i-1` is the
`m`-th occurrence of the value `a (i-1)`. Since a value has at most one `m`-th occurrence, the map
`i ↦ a (i-1)` is injective on the set `{i > N : a i = m}`, and its image consists of values that
occur at least `m` times. Conversely, whenever `i-1 ≥ N` is the `m`-th occurrence of some value
`v`, the next term is `m`. So the occurrences of the value `m` after the index `N` are in bijection
with the values whose `m`-th occurrence is at a position `≥ N`. Only finitely many values have
their `m`-th occurrence inside the initial segment `0,…,N` (there are only finitely many such
positions), so this bijection is exact "up to finitely many exceptions". In particular the two
infinitude statements are equivalent.

This is the structural backbone of the problem: it says the multiplicity function of the sequence
is its own conjugate. For `m = 1` it recovers `one_occurs_infinitely_often` (infinitely many
distinct values appear, so `1` recurs). For larger `m` it is the tool that pins down the eventual
multiplicity of every value: once only finitely many values occur `≥ m` times, the value `m` occurs
only finitely often. Bounding the recurrent values this way is precisely what confines the tail to
a small set of values and eventually forces one of the two parity subsequences to be periodic.
-/
lemma occurs_infinitely_iff_infinitely_many_values_occur_m_times
    {a : ℕ → ℕ} {N : ℕ} (h : Condition a N) :
    ∀ m, 1 ≤ m →
      ((∀ K, ∃ n, K ≤ n ∧ a n = m) ↔
        (∀ K, ∃ v, K ≤ v ∧
          ∃ L, m ≤ ((Finset.range L).filter (fun i => a i = v)).card)) := by
  obtain ⟨_, hrec⟩ := h
  intro m hm
  let cnt : ℕ → ℕ → ℕ := fun v L => ((Finset.range L).filter (fun i => a i = v)).card
  have hcnt0 : ∀ v, cnt v 0 = 0 := by intro v; simp only [cnt, Finset.range_zero,
    Finset.filter_empty, Finset.card_empty]
  have hcntmono : ∀ v, Monotone (cnt v) := by
    intro v x y hxy
    simp only [cnt]
    exact Finset.card_le_card (by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
      exact ⟨lt_of_lt_of_le hi.1 hxy, hi.2⟩)
  have hcntsucc : ∀ v L, cnt v (L+1) = cnt v L + (if a L = v then 1 else 0) := by
    intro v L
    simp only [cnt]
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hv : a L = v
    · simp only [hv, if_true]
      rw [Finset.card_insert_of_notMem]
      simp [Finset.mem_filter, Finset.mem_range]
    · simp [hv]
  constructor
  · -- Every value attaining `m` infinitely often is counted by infinitely many values.
    intro hinf K
    set T : Set ℕ := {n | N < n ∧ a n = m} with hT
    have hTinf : T.Infinite := by
      apply Set.infinite_of_forall_exists_gt
      intro b
      obtain ⟨n, hn, hna⟩ := hinf (max (b+1) (N+1))
      exact ⟨n, ⟨lt_of_lt_of_le (Nat.lt_succ_self N) (le_trans (le_max_right _ _) hn), hna⟩,
        lt_of_lt_of_le (Nat.lt_succ_self b) (le_trans (le_max_left _ _) hn)⟩
    have hinj : Set.InjOn (fun n => a (n-1)) T := by
      intro x hx y hy hxy
      change a (x-1) = a (y-1) at hxy
      obtain ⟨hxN, hxm⟩ := hx
      obtain ⟨hyN, hym⟩ := hy
      rcases lt_trichotomy x y with hlt | heq | hgt
      · exfalso
        have hcx : cnt (a (x-1)) x = m := (hrec x hxN).symm.trans hxm
        have hcy : cnt (a (x-1)) y = m := by
          have h : cnt (a (y-1)) y = m := (hrec y hyN).symm.trans hym
          rwa [← hxy] at h
        have hltc : cnt (a (x-1)) x < cnt (a (x-1)) y := by
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_subset_ne]
          constructor
          · intro i hi
            simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
            exact ⟨lt_of_lt_of_le hi.1 (le_of_lt hlt), hi.2⟩
          · intro heq'
            have hmem : y - 1 ∈ (Finset.range y).filter (fun i => a i = a (x-1)) := by
              simp only [Finset.mem_filter, Finset.mem_range]
              exact ⟨by omega, by rw [← hxy]⟩
            rw [← heq'] at hmem
            simp only [Finset.mem_filter, Finset.mem_range] at hmem
            omega
        omega
      · exact heq
      · exfalso
        have hcy : cnt (a (y-1)) y = m := (hrec y hyN).symm.trans hym
        have hcx : cnt (a (y-1)) x = m := by
          have h : cnt (a (x-1)) x = m := (hrec x hxN).symm.trans hxm
          rwa [hxy] at h
        have hltc : cnt (a (y-1)) y < cnt (a (y-1)) x := by
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_subset_ne]
          constructor
          · intro i hi
            simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
            exact ⟨lt_of_lt_of_le hi.1 (le_of_lt hgt), hi.2⟩
          · intro heq'
            have hmem : x - 1 ∈ (Finset.range x).filter (fun i => a i = a (y-1)) := by
              simp only [Finset.mem_filter, Finset.mem_range]
              exact ⟨by omega, by rw [hxy]⟩
            rw [← heq'] at hmem
            simp only [Finset.mem_filter, Finset.mem_range] at hmem
            omega
        omega
    have himg : ((fun n => a (n-1)) '' T).Infinite := (Set.infinite_image_iff hinj).2 hTinf
    obtain ⟨v, hvmem, hvK⟩ := himg.exists_gt K
    rw [Set.mem_image] at hvmem
    obtain ⟨n, hnT, hn'⟩ := hvmem
    obtain ⟨hnN, hnm⟩ := hnT
    refine ⟨v, le_of_lt hvK, n, ?_⟩
    have hcm : cnt (a (n-1)) n = m := (hrec n hnN).symm.trans hnm
    have : cnt v n = m := by rw [← hn']; exact hcm
    exact le_of_eq this.symm
  · -- Infinitely many values with multiplicity `≥ m` force `m` to recur.
    intro hinf2 K
    have hPN : N ≤ max N K := le_max_left _ _
    have hPK : K ≤ max N K := le_max_right _ _
    set B : ℕ := (Finset.range (max N K + 1)).sup a with hB
    obtain ⟨v, hvK, L, hL⟩ := hinf2 (max K (B + 1))
    have hvB : B < v :=
      lt_of_lt_of_le (Nat.lt_succ_self B) (le_trans (le_max_right K (B + 1)) hvK)
    have hfar : cnt v (max N K + 1) = 0 := by
      simp only [cnt]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i hi
      have hle : a i ≤ B := by rw [hB]; exact Finset.le_sup (f := a) hi
      omega
    have hex : ∃ t, m ≤ cnt v (t+1) := by
      refine ⟨L-1, ?_⟩
      have hL1 : 1 ≤ L := by
        rcases Nat.eq_zero_or_pos L with h0 | hp
        · subst h0
          simp only [Finset.range_zero, Finset.filter_empty, Finset.card_empty] at hL
          omega
        · exact hp
      rw [Nat.sub_add_cancel hL1]; exact hL
    set p : ℕ := Nat.find hex with hp
    have hpspec : m ≤ cnt v (p+1) := Nat.find_spec hex
    have hpmin : ∀ t < p, ¬ (m ≤ cnt v (t+1)) := fun t ht => Nat.find_min hex ht
    have hp_lt : cnt v p < m := by
      rcases Nat.eq_zero_or_pos p with hp0 | hppos
      · rw [hp0, hcnt0]; omega
      · have h := hpmin (p-1) (by omega)
        rw [Nat.sub_add_cancel (by omega : 1 ≤ p)] at h
        exact Nat.not_le.mp h
    have hcntp1 : cnt v (p+1) = m := by
      have hle : cnt v (p+1) ≤ m := by
        rw [hcntsucc]; split <;> omega
      omega
    have hap : a p = v := by
      by_contra hne
      have h := hcntsucc v p
      rw [if_neg hne] at h
      omega
    have hpge : max N K + 1 ≤ p := by
      by_contra hlt
      push_neg at hlt
      have hm1 : cnt v (p+1) ≤ cnt v (max N K + 1) :=
        hcntmono v (by omega)
      rw [hfar] at hm1
      omega
    refine ⟨p+1, by omega, ?_⟩
    rw [hrec (p+1) (by omega), show p + 1 - 1 = p from by omega, hap]
    exact hcntp1


end
