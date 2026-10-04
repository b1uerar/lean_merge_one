import Mathlib

open SimpleGraph Finset

abbrev Ladies := Fin 100

-- This is the main counting step: the degree of each board member fixes the
-- number of cross-edges, and the degree bound on each outside member then
-- forces it to be adjacent to every other outside member.
theorem balticway_2015_p7_outside_clique
    (had_tea : SimpleGraph Ladies) [DecidableRel had_tea.Adj]
    (h_had_tea_with_56 : ∀ l : Ladies, had_tea.degree l = 56)
    (board : Finset Ladies) (h_board_card : board.card = 50)
    (h_board_clique : had_tea.IsClique board) :
    had_tea.IsClique (↑(Finset.univ \ board) : Set Ladies) := by
  sorry

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
