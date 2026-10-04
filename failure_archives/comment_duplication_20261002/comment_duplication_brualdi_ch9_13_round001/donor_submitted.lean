import Mathlib

-- This is the regular bipartite multigraph factorization needed by the main
-- theorem: split each row-symbol multiplicity matrix into n assignments,
-- each of which uses every row once and each symbol r i times.
private theorem balanced_row_symbol_factor
    (m q n : ℕ) (r : Fin q → ℕ)
    (d : Fin m → Fin q → ℕ)
    (hn : 0 < n)
    (hrow : ∀ x, ∑ i : Fin q, d x i = n)
    (hsym : ∀ i, ∑ x : Fin m, d x i = n * r i) :
    ∃ g : Fin m → Fin q,
      (∀ x, 0 < d x (g x)) ∧
      (∀ i, (∑ x : Fin m, if g x = i then 1 else 0) = r i) := by
  classical
  let α := Σ i : Fin q, Fin (r i)
  let T : Fin m → Finset α := fun x =>
    Finset.univ.filter fun z => 0 < d x z.1
  have hrowTotal : (∑ x : Fin m, ∑ i : Fin q, d x i) = m * n := by
    calc
      _ = ∑ x : Fin m, n := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hrow x
      _ = m * n := by simp
  have hcolTotal : (∑ i : Fin q, ∑ x : Fin m, d x i) =
      n * ∑ i : Fin q, r i := by
    calc
      _ = ∑ i : Fin q, n * r i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hsym i
      _ = n * ∑ i : Fin q, r i := by rw [Finset.mul_sum]
  have hrSum : (∑ i : Fin q, r i) = m := by
    apply (Nat.eq_of_mul_eq_mul_left hn ?_).symm
    calc
      n * m = m * n := Nat.mul_comm _ _
      _ = ∑ x : Fin m, ∑ i : Fin q, d x i := hrowTotal.symm
      _ = ∑ i : Fin q, ∑ x : Fin m, d x i := Finset.sum_comm
      _ = n * ∑ i : Fin q, r i := hcolTotal
  have hall : ∀ s : Finset (Fin m), s.card ≤ (s.biUnion T).card := by
    intro s
    let A : Finset (Fin q) :=
      s.biUnion fun x => Finset.univ.filter fun i => 0 < d x i
    have hrowA : ∀ x, x ∈ s → (∑ i ∈ A, d x i) = n := by
      intro x hx
      calc
        (∑ i ∈ A, d x i) = ∑ i : Fin q, d x i := by
          apply Finset.sum_subset (Finset.subset_univ A)
          intro i hi hnot
          have hnonpos : ¬ 0 < d x i := by
            intro hp
            apply hnot
            simp only [A, Finset.mem_biUnion]
            exact ⟨x, hx, by simp [hp]⟩
          exact Nat.eq_zero_of_not_pos hnonpos
        _ = n := hrow x
    have hinc : n * s.card ≤ n * (∑ i ∈ A, r i) := by
      calc
        n * s.card = ∑ x ∈ s, ∑ i ∈ A, d x i := by
          calc
            n * s.card = ∑ x ∈ s, n := by simp [Nat.mul_comm]
            _ = ∑ x ∈ s, ∑ i ∈ A, d x i := by
              apply Finset.sum_congr rfl
              intro x hx
              exact (hrowA x hx).symm
        _ = ∑ i ∈ A, ∑ x ∈ s, d x i := Finset.sum_comm
        _ ≤ ∑ i ∈ A, ∑ x : Fin m, d x i := by
          apply Finset.sum_le_sum
          intro i hi
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
            (fun x hx hxs => Nat.zero_le _)
        _ = n * (∑ i ∈ A, r i) := by
          calc
            _ = ∑ i ∈ A, n * r i := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hsym i
            _ = n * (∑ i ∈ A, r i) := by rw [Finset.mul_sum]
    have hcard : (s.biUnion T).card = ∑ i ∈ A, r i := by
      have heq : s.biUnion T = A.sigma (fun i => Finset.univ) := by
        ext z
        rw [Finset.mem_sigma]
        simp [A, T, Finset.mem_biUnion, Finset.mem_filter]
      rw [heq, Finset.card_sigma]
      simp
    apply Nat.le_of_mul_le_mul_left ?_ hn
    rw [hcard]
    exact hinc
  obtain ⟨g', hg'inj, hg'mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' T).mp hall
  have hcardα : Fintype.card α = m := by
    dsimp [α]
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin, hrSum]
  have hbij : Function.Bijective g' :=
    (Fintype.bijective_iff_injective_and_card g').2
      ⟨hg'inj, by simp [Fintype.card_fin, hcardα]⟩
  let e : (Fin m) ≃ α := Equiv.ofBijective g' hbij
  let g : Fin m → Fin q := fun x => (g' x).1
  have hpos : ∀ x, 0 < d x (g x) := by
    intro x
    have hx := hg'mem x
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hx
  have hsigmaFiber : ∀ i : Fin q, {z : α // z.1 = i} ≃ Fin (r i) := by
    intro i
    refine
      { toFun := ?_
        invFun := fun k => ⟨⟨i, k⟩, rfl⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro z
      rcases z with ⟨⟨j, k⟩, hj⟩
      cases hj
      exact k
    · intro z
      rcases z with ⟨⟨j, k⟩, hj⟩
      cases hj
      rfl
    · intro k
      rfl
  have hcount (i : Fin q) :
      (∑ x : Fin m, if g x = i then 1 else 0) = r i := by
    let e' : {x : Fin m // g x = i} ≃ {z : α // z.1 = i} :=
      Equiv.subtypeEquiv e (fun x => by rfl)
    let ef : {x : Fin m // g x = i} ≃ Fin (r i) :=
      e'.trans (hsigmaFiber i)
    calc
      (∑ x : Fin m, if g x = i then 1 else 0) =
          Fintype.card {x : Fin m // g x = i} := by
        rw [Fintype.card_subtype]
        rw [Finset.card_filter]
      _ = Fintype.card (Fin (r i)) := Fintype.card_congr ef
      _ = r i := Fintype.card_fin _
  exact ⟨g, hpos, hcount⟩

private theorem balanced_row_symbol_decomposition_aux
    (m q n : ℕ) (r : Fin q → ℕ)
    (d : Fin m → Fin q → ℕ)
    (hrow : ∀ x, ∑ i : Fin q, d x i = n)
    (hsym : ∀ i, ∑ x : Fin m, d x i = n * r i) :
    ∃ f : Fin n → Fin m → Fin q,
      (∀ x i, (∑ t : Fin n, if f t x = i then 1 else 0) = d x i) ∧
      (∀ t i, (∑ x : Fin m, if f t x = i then 1 else 0) = r i) := by
  revert d hrow hsym
  induction n with
  | zero =>
      intro d hrow hsym
      have hdzero : ∀ x i, d x i = 0 := by
        intro x i
        have hle : d x i ≤ ∑ j : Fin q, d x j :=
          Finset.single_le_sum (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
        rw [hrow x] at hle
        exact Nat.eq_zero_of_le_zero hle
      refine ⟨Fin.elim0, ?_, ?_⟩
      · intro x i
        simp [hdzero x i]
      · intro t
        exact Fin.elim0 t
  | succ n ih =>
      intro d hrow hsym
      have hrowPos : ∀ x, ∑ i : Fin q, d x i = n + 1 := hrow
      have hsymPos : ∀ i, ∑ x : Fin m, d x i = (n + 1) * r i := hsym
      obtain ⟨g, hgpos, hgcount⟩ :=
        balanced_row_symbol_factor m q (n + 1) r d (Nat.succ_pos n) hrowPos hsymPos
      let e : Fin m → Fin q → ℕ := fun x i => if g x = i then 1 else 0
      let d' : Fin m → Fin q → ℕ := fun x i => d x i - e x i
      have hle : ∀ x i, e x i ≤ d x i := by
        intro x i
        dsimp [e]
        split_ifs with h
        · subst i
          exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (hgpos x))
        · exact Nat.zero_le _
      have hdecomp : ∀ x i, d x i = d' x i + e x i := by
        intro x i
        exact (Nat.sub_add_cancel (hle x i)).symm
      have hrow' : ∀ x, ∑ i : Fin q, d' x i = n := by
        intro x
        have hselsum : (∑ i : Fin q, e x i) = 1 := by
          dsimp [e]
          rw [Finset.sum_ite_eq Finset.univ (g x) (fun _ => 1)]
          simp
        have hsum := hrowPos x
        rw [show (∑ i : Fin q, d x i) =
            (∑ i : Fin q, d' x i) + ∑ i : Fin q, e x i by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro i hi
              exact hdecomp x i] at hsum
        rw [hselsum] at hsum
        omega
      have hsym' : ∀ i, ∑ x : Fin m, d' x i = n * r i := by
        intro i
        have hsum := hsymPos i
        rw [show (∑ x : Fin m, d x i) =
            (∑ x : Fin m, d' x i) + ∑ x : Fin m, e x i by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro x hx
              exact hdecomp x i] at hsum
        rw [hgcount i] at hsum
        nlinarith
      obtain ⟨f', hf'row, hf'col⟩ := ih d' hrow' hsym'
      let f : Fin (n + 1) → Fin m → Fin q :=
        Fin.cases g (fun t => f' t)
      refine ⟨f, ?_, ?_⟩
      · intro x i
        calc
          (∑ t : Fin (n + 1), if f t x = i then 1 else 0) =
              (if g x = i then 1 else 0) +
                ∑ t : Fin n, if f' t x = i then 1 else 0 := by
            rw [Fin.sum_univ_succ]
            simp [f]
          _ = d x i := by
            rw [hf'row x i]
            dsimp [d', e]
            split_ifs with h
            · subst i
              calc
                1 + (d x (g x) - 1) = (d x (g x) - 1) + 1 := Nat.add_comm _ _
                _ = d x (g x) :=
                  Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
                    (Nat.ne_of_gt (hgpos x)))
            · omega
      · intro t i
        cases t using Fin.cases with
        | zero =>
            exact hgcount i
        | succ t =>
            exact hf'col t i

theorem balanced_row_symbol_decomposition
    (m q n : ℕ) (r : Fin q → ℕ)
    (d : Fin m → Fin q → ℕ)
    (hn : 0 < n)
    (hrow : ∀ x, ∑ i : Fin q, d x i = n)
    (hsym : ∀ i, ∑ x : Fin m, d x i = n * r i) :
    ∃ f : Fin n → Fin m → Fin q,
      (∀ x i, (∑ t : Fin n, if f t x = i then 1 else 0) = d x i) ∧
      (∀ t i, (∑ x : Fin m, if f t x = i then 1 else 0) = r i) := by
  exact balanced_row_symbol_decomposition_aux m q n r d hrow hsym
