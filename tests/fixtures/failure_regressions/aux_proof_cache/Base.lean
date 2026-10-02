import Mathlib
section


open scoped Finset


-- The condition of the problem. Following usual Lean conventions, this is expressed with indices starting from 0, rather than from 1 as in the informal statement (but `N` remains as the index of the last term for which `a n` is not defined in terms of previous terms).
def Condition (a : ℕ → ℕ) (N : ℕ) : Prop :=
  (∀ i, 0 < a i) ∧ ∀ n, N < n → a n = #{i ∈ Finset.range n | a i = a (n - 1)}


end

section


open scoped Finset


-- The property of a sequence being eventually periodic.


lemma one_occurs_infinitely_often {a : ℕ → ℕ} {N : ℕ} (h : Condition a N) :
    ∀ M, ∃ n, M ≤ n ∧ a n = 1 := by
  obtain ⟨_, hrec⟩ := h
  by_contra hcon
  push_neg at hcon
  obtain ⟨M, hM⟩ := hcon
  set K : ℕ := max M N + 1 with hKdef
  -- Step 1: from index `K` on, every value already occurred before `K`.
  have hnew : ∀ n, K ≤ n → ∃ i, i < K ∧ a i = a n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      by_contra hc
      push_neg at hc
      have hfilter : (Finset.range (n + 1)).filter (fun i => a i = a n) = {n} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        constructor
        · rintro ⟨hi, hai⟩
          by_contra hne
          have hilt : i < n := by omega
          rcases lt_or_ge i K with hik | hik
          · exact hc i hik hai
          · obtain ⟨j, hjK, hja⟩ := ih i hilt hik
            exact hc j hjK (hja.trans hai)
        · rintro rfl
          exact ⟨by omega, rfl⟩
      have hcard : ((Finset.range (n + 1)).filter (fun i => a i = a n)).card = 1 := by
        rw [hfilter]; simp
      have hval : a (n + 1) = 1 := by
        have h1 := hrec (n + 1) (by omega)
        rw [show n + 1 - 1 = n from by omega] at h1
        rw [hcard] at h1
        exact h1
      exact hM (n + 1) (by omega) hval
  set S : Finset ℕ := (Finset.range K).image a with hSdef
  set B : ℕ := (Finset.range K).sup a with hBdef
  have hle : ∀ n, K ≤ n → a n ≤ B := by
    intro n hn
    obtain ⟨j, hjK, hja⟩ := hnew n hn
    have hjmem : j ∈ Finset.range K := Finset.mem_range.mpr hjK
    have hsup : a j ≤ (Finset.range K).sup a := Finset.le_sup (f := a) hjmem
    rw [hBdef, ← hja]
    exact hsup
  -- Step 2: pigeonhole contradiction.
  have hf : ∀ x ∈ Finset.Ico K (K + B * S.card + 1), a x ∈ S := by
    intro x hx
    have hxK : K ≤ x := (Finset.mem_Ico.mp hx).1
    obtain ⟨j, hjK, hja⟩ := hnew x hxK
    rw [hSdef]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hjK, hja⟩
  have hncard : S.card * B < (Finset.Ico K (K + B * S.card + 1)).card := by
    have hc : (Finset.Ico K (K + B * S.card + 1)).card = B * S.card + 1 := by
      simp
      omega
    calc S.card * B = B * S.card := Nat.mul_comm _ _
      _ < B * S.card + 1 := Nat.lt_succ_self _
      _ = (Finset.Ico K (K + B * S.card + 1)).card := hc.symm
  obtain ⟨v, hvS, hvB⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := Finset.Ico K (K + B * S.card + 1)) (t := S) (f := a) (n := B) hf hncard
  let F : Finset ℕ := (Finset.Ico K (K + B * S.card + 1)).filter (fun x => a x = v)
  have hFcard : B < F.card := hvB
  have hFne : F.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p, hpF, hpmax⟩ := Finset.exists_max_image F id hFne
  have hpK : K ≤ p := (Finset.mem_Ico.mp (Finset.mem_filter.mp hpF).1).1
  have hpa : a p = v := (Finset.mem_filter.mp hpF).2
  have hsub : F ⊆ (Finset.range (p + 1)).filter (fun i => a i = v) := by
    intro x hx
    rw [Finset.mem_filter]
    have hxp : x ≤ p := by simpa using hpmax x hx
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hxp),
      (Finset.mem_filter.mp hx).2⟩
  have hfiber_le : F.card ≤ ((Finset.range (p + 1)).filter (fun i => a i = v)).card :=
    Finset.card_le_card hsub
  have hcount : ((Finset.range (p + 1)).filter (fun i => a i = v)).card = a (p + 1) := by
    have h1 := hrec (p + 1) (by omega)
    rw [show p + 1 - 1 = p from by omega] at h1
    rw [← hpa]
    exact h1.symm
  have hbound : ((Finset.range (p + 1)).filter (fun i => a i = v)).card ≤ B := by
    rw [hcount]; exact hle (p + 1) (by omega)
  omega


end




-- The condition of the problem. Following usual Lean conventions, this is expressed with indices starting from 0, rather than from 1 as in the informal statement (but `N` remains as the index of the last term for which `a n` is not defined in terms of previous terms).


-- The property of a sequence being eventually periodic.
def EventuallyPeriodic (b : ℕ → ℕ) : Prop := ∃ p M, 0 < p ∧ ∀ m, M ≤ m → b (m + p) = b m


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
  sorry


end



/--
Let $a_1, a_2, a_3, \dots$ be an infinite sequence of positive integers, and let $N$ be a positive integer. Suppose that, for each $n > N$, $a_n$ is equal to the number of times $a_{n-1}$ appears in the list $a_1, a_2, \dots, a_{n-1}$. Prove that at least one of the sequence $a_1, a_3, a_5, \dots$ and $a_2, a_4, a_6, \dots$ is eventually periodic. (An infinite sequence $b_1, b_2, b_3, \dots$ is eventually periodic if there exist positive integers $p$ and $M$ such that $b_{m+p} = b_m$ for all $m \ge M$.)
-/
theorem imo_2024_p3 {a : ℕ → ℕ} {N : ℕ} (h : Condition a N) :
    EventuallyPeriodic (fun i ↦ a (2 * i)) ∨ EventuallyPeriodic (fun i ↦ a (2 * i + 1)) := by sorry
