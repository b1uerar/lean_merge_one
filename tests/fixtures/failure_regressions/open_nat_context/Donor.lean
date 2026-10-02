import Mathlib

open Nat
open Equiv Finset

def f {m : ℕ} (n : Finset.Icc 1 m → ℤ) (x : Equiv.Perm (Finset.Icc 1 m)) : ℤ := ∑ i, x i * n i

lemma sum_perm_fin_apply_zero (n : ℕ) (w : Fin (n + 1) → ℤ) :
    (∑ a : Perm (Fin (n + 1)), w (a 0)) = (n ! : ℤ) * ∑ j : Fin (n + 1), w j := by
  rw [Finset.univ_perm_fin_succ]
  simp only [Finset.sum_map, Equiv.Perm.decomposeFin_symm_apply_zero, Fintype.sum_prod_type,
    Equiv.toEmbedding_apply]
  simp
  rw [Fintype.card_perm, Fintype.card_fin, ← Finset.mul_sum]

lemma sum_perm_fin_apply (n : ℕ) (k : Fin n) (w : Fin n → ℤ) :
    (∑ a : Perm (Fin n), w (a k)) = ((n - 1)! : ℤ) * ∑ j : Fin n, w j := by
  cases n with
  | zero => exact Fin.elim0 k
  | succ n =>
      let τ : Perm (Fin (n + 1)) := Equiv.swap 0 k
      have hτ : τ 0 = k := by simp [τ]
      calc
        (∑ a : Perm (Fin (n + 1)), w (a k))
            = ∑ a : Perm (Fin (n + 1)), w ((a * τ) 0) := by
              simp [Equiv.Perm.mul_apply, hτ]
        _ = ∑ b : Perm (Fin (n + 1)), w (b 0) := by
              simpa only [Equiv.coe_mulRight] using
                (Equiv.sum_comp (Equiv.mulRight τ)
                  (fun b : Perm (Fin (n + 1)) => w (b 0)))
        _ = (n ! : ℤ) * ∑ j : Fin (n + 1), w j := sum_perm_fin_apply_zero n w

lemma sum_perm_apply_eq (α : Type*) [Fintype α] [DecidableEq α] (i : α) (w : α → ℤ) :
    (∑ a : Perm α, w (a i)) = ((Fintype.card α - 1)! : ℤ) * ∑ j : α, w j := by
  classical
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  have h := sum_perm_fin_apply (Fintype.card α) (e i)
    (fun k : Fin (Fintype.card α) => w (e.symm k))
  calc
    (∑ a : Perm α, w (a i))
        = ∑ a : Perm α,
            (fun k : Fin (Fintype.card α) => w (e.symm k)) (e.permCongr a (e i)) := by
          apply Finset.sum_congr rfl
          intro a _
          simp [Equiv.permCongr_apply]
    _ = ∑ b : Perm (Fin (Fintype.card α)),
            (fun k : Fin (Fintype.card α) => w (e.symm k)) (b (e i)) := by
          simpa using
            (Equiv.sum_comp e.permCongr
              (fun b : Perm (Fin (Fintype.card α)) => w (e.symm (b (e i)))))
    _ = ((Fintype.card α - 1)! : ℤ) *
          ∑ k : Fin (Fintype.card α), w (e.symm k) := h
    _ = ((Fintype.card α - 1)! : ℤ) * ∑ j : α, w j := by
          rw [Equiv.sum_comp e.symm w]

lemma sum_Icc_one_id (m : ℕ) : (∑ j ∈ Finset.Icc 1 m, j) = m * (m + 1) / 2 := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_comm, Nat.add_sub_cancel]
  rw [Finset.sum_add_distrib, Finset.sum_range_id, Finset.sum_const, Finset.card_range,
    smul_eq_mul]
  rw [mul_one, add_comm]
  apply Nat.eq_div_of_mul_eq_right (by norm_num : (2 : ℕ) ≠ 0)
  have h2 : 2 ∣ m * (m - 1) := Even.two_dvd (Nat.even_mul_pred_self m)
  rw [Nat.mul_add, Nat.mul_div_cancel' h2]
  rcases m with _ | m
  · simp
  · simp only [Nat.add_sub_cancel]
    ring

lemma sum_Icc_one_id_int (m : ℕ) :
    (∑ j : Finset.Icc 1 m, (j : ℤ)) = ((m * (m + 1) / 2 : ℕ) : ℤ) := by
  rw [Finset.sum_coe_sort]
  rw [← Nat.cast_sum, sum_Icc_one_id]

lemma sum_perm_Icc_apply (m : ℕ) (i : Finset.Icc 1 m) :
    (∑ a : Perm (Finset.Icc 1 m), (a i : ℤ)) =
      ((m - 1)! : ℤ) * ((m * (m + 1) / 2 : ℕ) : ℤ) := by
  have h := sum_perm_apply_eq (Finset.Icc 1 m) i (fun j : Finset.Icc 1 m => (j : ℤ))
  rw [show (∑ j : Finset.Icc 1 m, (j : ℤ)) = ((m * (m + 1) / 2 : ℕ) : ℤ) from
    sum_Icc_one_id_int m] at h
  simpa using h


/--
For odd `m`, the sum of `f n a` over all permutations `a` is divisible by `m!`.

This is the arithmetic half of the contradiction argument for `imo_2001_p4`.  If no two
permutations gave congruent values modulo `m!`, then the residues of `f n a` would run through
all of `0, …, m! - 1`; hence their sum would be congruent to
`m! * (m! - 1) / 2`.  Since `m > 1`, that triangular number is not divisible by `m!`, so the
divisibility established here would force a collision and prove the goal.  Averaging over all
permutations gives the factor `(m - 1)! * (1 + ⋯ + m) = m! * (m + 1) / 2`, where oddness of
`m` is exactly what makes the quotient integral.
-/
lemma sum_perm_f_dvd_factorial {m : ℕ} (hm : Odd m) (n : Finset.Icc 1 m → ℤ) :
    (m ! : ℤ) ∣ ∑ a : Equiv.Perm (Finset.Icc 1 m), f n a := by
  have htwo : 2 ∣ m + 1 := (hm.add_odd odd_one).two_dvd
  have hmpos : 0 < m := hm.pos
  let T : ℤ := ∑ i : Finset.Icc 1 m, n i
  have hsum :
      (∑ a : Perm (Finset.Icc 1 m), f n a) =
        ((m ! : ℕ) : ℤ) * (((m + 1) / 2 : ℕ) : ℤ) * T := by
    unfold f
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    simp_rw [sum_perm_Icc_apply]
    rw [← Finset.mul_sum]
    change (((m - 1)! : ℤ) * ((m * (m + 1) / 2 : ℕ) : ℤ) * T) =
      ((m ! : ℕ) : ℤ) * (((m + 1) / 2 : ℕ) : ℤ) * T
    have hquot : ((m * (m + 1) / 2 : ℕ) : ℤ) = (m : ℤ) * (((m + 1) / 2 : ℕ) : ℤ) := by
      rw [Nat.mul_div_assoc m htwo, Nat.cast_mul]
    have hfact : ((m - 1)! : ℤ) * (m : ℤ) = (m ! : ℤ) := by
      norm_num only [← Nat.cast_mul]
      rw [Nat.mul_comm, Nat.mul_factorial_pred hmpos.ne']
    rw [hquot]
    rw [← mul_assoc, hfact]
  rw [hsum]
  rw [mul_assoc]
  exact dvd_mul_right _ _
