import Mathlib
section


def tripleFn {α : Type} (x y z : α) : Fin 3 → α := ![x, y, z]


def Single (a : ℕ) :=
  { f : Fin 3 → Fin (a + 1) // (∑ i, (f i).val) = a }


noncomputable instance singleFintype (a : ℕ) : Fintype (Single a) :=
  by
    classical
    unfold Single
    exact Fintype.subtype
      (Finset.univ.filter (fun f : Fin 3 → Fin (a + 1) => (∑ i, (f i).val) = a))
      (by intro f; simp)


def singleEncode (a : ℕ) (f : Single a) : Sym2 (Fin (a + 1)) :=
  Sym2.mk (f.val 0,
    ⟨(f.val 0).val + (f.val 1).val, by
      have hs := f.property
      simp [Fin.sum_univ_succ] at hs
      omega⟩)


def singleDecode (a : ℕ) (s : Sym2 (Fin (a + 1))) : Single a :=
  let p := (Sym2.sortEquiv (α := Fin (a + 1))) s
  let x := p.val.1.val
  let y := p.val.2.val - p.val.1.val
  let z := a - p.val.2.val
  ⟨tripleFn ⟨x, by
      have hlt := p.val.1.isLt
      omega⟩ ⟨y, by
      have hp := p.property
      have hpv := Fin.le_iff_val_le_val.mp hp
      have hlt := p.val.2.isLt
      omega⟩ ⟨z, by
      have hlt := p.val.2.isLt
      omega⟩, by
    simp [tripleFn, Fin.sum_univ_succ]
    have hp := p.property
    have hpv := Fin.le_iff_val_le_val.mp hp
    have hlt := p.val.2.isLt
    omega⟩


noncomputable def singleEquiv (a : ℕ) :
    Single a ≃ Sym2 (Fin (a + 1)) where
  toFun := singleEncode a
  invFun := singleDecode a
  left_inv := by
    intro f
    apply Subtype.ext
    have hs := f.property
    simp [Fin.sum_univ_succ] at hs
    have hxy : f.val 0 ≤
        (⟨(f.val 0).val + (f.val 1).val, by omega⟩ : Fin (a + 1)) := by
      exact Fin.le_iff_val_le_val.mpr (Nat.le_add_right _ _)
    have hsort :
        (Sym2.sortEquiv (α := Fin (a + 1))) (singleEncode a f) =
          ⟨(f.val 0, ⟨(f.val 0).val + (f.val 1).val, by omega⟩), hxy⟩ := by
      simp [singleEncode, Sym2.sortEquiv, Sym2.inf_mk, Sym2.sup_mk,
        inf_eq_left.mpr hxy, sup_eq_right.mpr hxy]
    funext i
    fin_cases i <;>
      apply Fin.ext <;>
      simp [singleDecode, hsort, tripleFn] <;> omega
  right_inv := by
    intro s
    have hleval : s.inf.val ≤ s.sup.val :=
      Fin.le_iff_val_le_val.mp (Sym2.inf_le_sup s)
    apply (Sym2.sortEquiv (α := Fin (a + 1))).injective
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;>
      simp [singleEncode, singleDecode, tripleFn,
        Sym2.sortEquiv, Sym2.inf_mk, Sym2.sup_mk, hleval]


theorem single_card (a : ℕ) :
    Fintype.card (Single a) = Nat.choose (a + 2) 2 := by
  classical
  calc
    Fintype.card (Single a) = Fintype.card (Sym2 (Fin (a + 1))) :=
      Fintype.card_congr (singleEquiv a)
    _ = Nat.choose (Fintype.card (Fin (a + 1)) + 1) 2 := Sym2.card
    _ = Nat.choose (a + 2) 2 := by simp


def PairDomain (a b : ℕ) :=
  {f : Fin 3 → Fin (a + 1) × Fin (b + 1) //
    (∑ i, (f i).1.val) = a ∧ (∑ i, (f i).2.val) = b}


noncomputable instance pairDomainFintype (a b : ℕ) : Fintype (PairDomain a b) := by
  classical
  unfold PairDomain
  exact Fintype.subtype
    (Finset.univ.filter (fun f : Fin 3 → Fin (a + 1) × Fin (b + 1) =>
      (∑ i, (f i).1.val) = a ∧ (∑ i, (f i).2.val) = b))
    (by intro f; simp)


noncomputable def pairSplitEquiv (a b : ℕ) :
    PairDomain a b ≃ Single a × Single b where
  toFun f :=
    (⟨fun i => (f.val i).1, by
      simpa [Fin.sum_univ_succ] using f.property.1⟩,
     ⟨fun i => (f.val i).2, by
      simpa [Fin.sum_univ_succ] using f.property.2⟩)
  invFun uv :=
    ⟨fun i => (uv.1.val i, uv.2.val i),
      ⟨by simpa [Fin.sum_univ_succ] using uv.1.property,
       by simpa [Fin.sum_univ_succ] using uv.2.property⟩⟩
  left_inv := by
    intro f
    apply Subtype.ext
    funext i
    rfl
  right_inv := by
    rintro ⟨x, y⟩
    apply Prod.ext
    · apply Subtype.ext
      funext i
      rfl
    · apply Subtype.ext
      funext i
      rfl


theorem pair_card (a b : ℕ) :
    (Finset.univ.filter (fun f : Fin 3 → Fin (a + 1) × Fin (b + 1) =>
      (∑ i, (f i).1.val) = a ∧ (∑ i, (f i).2.val) = b)).card =
      Nat.choose (a + 2) 2 * Nat.choose (b + 2) 2 := by
  classical
  let pred : (Fin 3 → Fin (a + 1) × Fin (b + 1)) → Prop :=
    fun f => (∑ i, (f i).1.val) = a ∧ (∑ i, (f i).2.val) = b
  have hcard :
      Fintype.card (PairDomain a b) =
        (Finset.univ.filter pred).card := by
    exact Fintype.card_of_subtype (Finset.univ.filter pred) (by
      intro f
      simp [pred])
  calc
    _ = Fintype.card (PairDomain a b) := hcard.symm
    _ = Fintype.card (Single a × Single b) :=
      Fintype.card_congr (pairSplitEquiv a b)
    _ = Nat.choose (a + 2) 2 * Nat.choose (b + 2) 2 := by
      rw [Fintype.card_prod, single_card, single_card]



-- This counts the bounded allocation pairs by separating the two fruit
-- totals into independent weak-composition counts.
theorem fin3_pair_sum_count (a b : ℕ) :
    (Finset.univ.filter (fun f : Fin 3 → Fin (a + 1) × Fin (b + 1) =>
      (∑ i, (f i).1.val) = a ∧ (∑ i, (f i).2.val) = b)).card =
        Nat.choose (a + 2) 2 * Nat.choose (b + 2) 2 := by
  exact pair_card a b


end



-- This counts the bounded allocation pairs by separating the two fruit
-- totals into independent weak-composition counts.


/--
How many different ways can three people divide seven pears and five apples?
-/
theorem hackmath_10 (sols : Finset (Fin 3 → (ℕ × ℕ)))
    (h_sols : ∀ f, f ∈ sols ↔ (∑ i, (f i).1 = 7 ∧ ∑ i, (f i).2 = 5)) :
    sols.card = ((756) : ℕ ) := by sorry
