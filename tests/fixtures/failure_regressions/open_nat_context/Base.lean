import Mathlib

open Nat

def f {m : ℕ} (n : Finset.Icc 1 m → ℤ) (x : Equiv.Perm (Finset.Icc 1 m)) : ℤ := ∑ i, x i * n i

/--
Let $n_1, n_2, \dots , n_m$ be integers where $m>1$ is odd. Let $x = (x_1, \dots , x_m)$ denote a permutation of the integers $1, 2, \cdots , m$. Let $f(x) = x_1n_1 + x_2n_2 + ... + x_mn_m$. Show that for some distinct permutations $a$, $b$ the difference $f(a) - f(b)$ is a multiple of $m!$.
-/
theorem imo_2001_p4 (m : ℕ) (h_m_pos: m > 1) (h_m_odd: Odd m) (n : Finset.Icc 1 m → ℤ):
    ∃ a b : Equiv.Perm (Finset.Icc 1 m), a ≠ b ∧ ↑(m !) ∣ (f n a - f n b) := by sorry

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
  sorry
