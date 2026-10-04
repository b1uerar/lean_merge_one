import Mathlib
section


open SimpleGraph Finset


abbrev Ladies := Fin 100


end

section


open SimpleGraph Finset


-- This is the main counting step: the degree of each board member fixes the
-- number of cross-edges, and the degree bound on each outside member then
-- forces it to be adjacent to every other outside member.
theorem balticway_2015_p7_outside_clique
    (had_tea : SimpleGraph Ladies) [DecidableRel had_tea.Adj]
    (h_had_tea_with_56 : ∀ l : Ladies, had_tea.degree l = 56)
    (board : Finset Ladies) (h_board_card : board.card = 50)
    (h_board_clique : had_tea.IsClique board) :
    had_tea.IsClique (↑(Finset.univ \ board) : Set Ladies) := by
  classical
  let outside : Finset Ladies := Finset.univ \ board
  let cross : SimpleGraph Ladies :=
    had_tea.between (board : Set Ladies) (outside : Set Ladies)
  have hbi : cross.IsBipartiteWith (board : Set Ladies) (outside : Set Ladies) := by
    apply SimpleGraph.between_isBipartiteWith
    apply Set.disjoint_left.mpr
    intro x hxBoard hxOutside
    have hxOutside' : x ∉ board := by simpa [outside] using hxOutside
    exact hxOutside' hxBoard
  have houtside_card : outside.card = 50 := by
    dsimp [outside]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ board)]
    simp [h_board_card]
  have hcl : ∀ {u v : Ladies}, u ∈ board → v ∈ board → u ≠ v →
      had_tea.Adj u v := by
    intro u v hu hv huv
    exact h_board_clique (by simpa using hu) (by simpa using hv) huv
  have hcross_board : ∀ b ∈ board, cross.degree b = 7 := by
    intro b hb
    have hA : had_tea.neighborFinset b ∩ board = board.erase b := by
      ext y
      simp only [Finset.mem_inter, Finset.mem_erase]
      constructor
      · rintro ⟨hby, hy⟩
        exact ⟨((had_tea.mem_neighborFinset b y).mp hby).ne.symm, hy⟩
      · rintro ⟨hyb, hy⟩
        exact ⟨(had_tea.mem_neighborFinset b y).mpr (hcl hb hy hyb.symm), hy⟩
    have hBcard : #(had_tea.neighborFinset b \ board) = 7 := by
      have hp := Finset.card_inter_add_card_sdiff (had_tea.neighborFinset b) board
      rw [hA, Finset.card_erase_of_mem hb, h_board_card,
        SimpleGraph.card_neighborFinset_eq_degree, h_had_tea_with_56] at hp
      omega
    have hCn : cross.neighborFinset b = had_tea.neighborFinset b \ board := by
      ext y
      simp [cross, SimpleGraph.between, outside, hb]
    calc
      cross.degree b = #(cross.neighborFinset b) := by
        rw [cross.card_neighborFinset_eq_degree]
      _ = #(had_tea.neighborFinset b \ board) := by rw [hCn]
      _ = 7 := hBcard
  have hleft : (∑ b ∈ board, cross.degree b) = 350 := by
    calc
      (∑ b ∈ board, cross.degree b) = ∑ b ∈ board, 7 := by
        apply Finset.sum_congr rfl
        intro b hb
        exact hcross_board b hb
      _ = 350 := by norm_num [Finset.sum_const_nat, h_board_card]
  have hright : (∑ x ∈ outside, cross.degree x) = 350 := by
    calc
      (∑ x ∈ outside, cross.degree x) = ∑ b ∈ board, cross.degree b :=
        (SimpleGraph.isBipartiteWith_sum_degrees_eq hbi).symm
      _ = 350 := hleft
  have hcross_lower : ∀ x ∈ outside, 7 ≤ cross.degree x := by
    intro x hx
    let N := had_tea.neighborFinset x
    have hxnot : x ∉ board := by
      simpa [outside] using hx
    have hCn : cross.neighborFinset x = N ∩ board := by
      ext y
      simp [cross, N, SimpleGraph.between, outside, hxnot]
    have hsub : N \ board ⊆ outside.erase x := by
      intro y hy
      have hyN : y ∈ N := (Finset.mem_sdiff.mp hy).1
      have hynot : y ∉ board := (Finset.mem_sdiff.mp hy).2
      have hyx : y ≠ x := by
        intro h
        subst y
        exact SimpleGraph.notMem_neighborFinset_self had_tea x hyN
      exact Finset.mem_erase.mpr ⟨hyx, by simp [outside, hynot]⟩
    have hBbound : #(N \ board) ≤ 49 := by
      calc
        #(N \ board) ≤ #(outside.erase x) := Finset.card_le_card hsub
        _ = 49 := by
          rw [Finset.card_erase_of_mem hx, houtside_card]
    have hp := Finset.card_inter_add_card_sdiff N board
    rw [SimpleGraph.card_neighborFinset_eq_degree, h_had_tea_with_56] at hp
    rw [← hCn, cross.card_neighborFinset_eq_degree] at hp
    omega
  have hconst : (∑ x ∈ outside, (7 : ℕ)) = 350 := by
    norm_num [Finset.sum_const_nat, houtside_card]
  have hsum_eq : (∑ x ∈ outside, (7 : ℕ)) =
      ∑ x ∈ outside, cross.degree x := hconst.trans hright.symm
  have hcross_outside : ∀ x ∈ outside, cross.degree x = 7 := by
    have heq := (Finset.sum_eq_sum_iff_of_le
      (s := outside) (f := fun _ => (7 : ℕ)) (g := fun x => cross.degree x)
      (by intro x hx; exact hcross_lower x hx)).mp hsum_eq
    intro x hx
    exact (heq x hx).symm
  intro x hx y hy hxy
  have hxnot : x ∉ board := by
    simpa [outside] using hx
  have hNset : had_tea.neighborFinset x \ board = outside.erase x := by
    have hCn : cross.neighborFinset x =
        had_tea.neighborFinset x ∩ board := by
      ext z
      simp [cross, SimpleGraph.between, outside, hxnot]
    have hBcard : #(had_tea.neighborFinset x \ board) = 49 := by
      have hp := Finset.card_inter_add_card_sdiff
        (had_tea.neighborFinset x) board
      rw [← hCn, cross.card_neighborFinset_eq_degree,
        hcross_outside x hx, SimpleGraph.card_neighborFinset_eq_degree,
        h_had_tea_with_56] at hp
      omega
    have hsub : had_tea.neighborFinset x \ board ⊆ outside.erase x := by
      intro z hz
      have hzN : z ∈ had_tea.neighborFinset x :=
        (Finset.mem_sdiff.mp hz).1
      have hznot : z ∉ board := (Finset.mem_sdiff.mp hz).2
      have hzx : z ≠ x := by
        intro h
        subst z
        exact SimpleGraph.notMem_neighborFinset_self had_tea x hzN
      exact Finset.mem_erase.mpr ⟨hzx, by simp [outside, hznot]⟩
    have htarget : #(outside.erase x) = 49 := by
      rw [Finset.card_erase_of_mem hx, houtside_card]
    have hcardle :
        #(outside.erase x) ≤ #(had_tea.neighborFinset x \ board) := by
      rw [htarget, hBcard]
    exact Finset.eq_of_subset_of_card_le hsub hcardle
  have hyErase : y ∈ outside.erase x :=
    Finset.mem_erase.mpr ⟨hxy.symm, hy⟩
  have hyN : y ∈ had_tea.neighborFinset x := by
    have hyDiff : y ∈ had_tea.neighborFinset x \ board := by
      rw [hNset]
      exact hyErase
    exact (Finset.mem_sdiff.mp hyDiff).1
  exact (had_tea.mem_neighborFinset x y).mp hyN


end


open SimpleGraph Finset



-- This is the main counting step: the degree of each board member fixes the
-- number of cross-edges, and the degree bound on each outside member then
-- forces it to be adjacent to every other outside member.


/--
There are 100 members in a ladies' club. Each lady has had tea (in private) with exactly 56 of the other members of the club. The Board, consisting of the 50 most distinguished ladies, have all had tea with one another. Prove that the entire club may be split into two groups in such a way that, within each group, any lady has had tea with any other.
-/
theorem balticway_2015_p7 (had_tea: SimpleGraph (Ladies)) [DecidableRel had_tea.Adj]
    (h_had_tea_with_56: ∀ l : Ladies, had_tea.degree l = 56)
    (h_board: ∃ board : Finset Ladies, board.card = 50 ∧ had_tea.IsClique board) :
    ∃ group1 group2: Finset Ladies,
      group1 ∪ group2 = Finset.univ
      ∧ Disjoint group1 group2
      ∧ had_tea.IsClique group1
      ∧ had_tea.IsClique group2  := by
  obtain ⟨board, h_board_card, h_board_clique⟩ := h_board
  refine ⟨board, Finset.univ \ board, ?_, ?_, h_board_clique, ?_⟩
  · ext x
    simp
  · rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_sdiff.mp hx').2 hx
  · exact balticway_2015_p7_outside_clique had_tea h_had_tea_with_56
      board h_board_card h_board_clique
