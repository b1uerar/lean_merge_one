import Mathlib

def clean (S : Set ℕ+) (n : ℕ) : Prop :=
  ∃! (S' : Finset ℕ+),
    ((S' : Set _) ⊆ S) ∧ (Odd S'.card) ∧ (∑ s ∈ S', (s : ℕ) = n)

-- In a contradiction argument where all sufficiently large integers are clean,
-- this lets us track the unique representation after exchanging one element.


-- This proves the finite-set case of the main theorem by bounding every
-- possible representation by the sum of all elements of S.


-- Appending an element outside both representations converts equal even
-- representations into odd ones, where eventual cleanliness forces equality.


-- Any representation of a clean number below a cutoff uses only elements
-- below that cutoff, which makes finite initial segments control such sums.


-- If every integer past N is clean, the clean integers before a cutoff t
-- must all be supplied by odd subsets of F; counting those subsets bounds
-- how quickly the finite initial segment can grow.
theorem clean_tail_bounds_finite_cutoff
    (S : Set ℕ+) (N t : ℕ) (F : Finset ℕ+)
    (hclean : ∀ n : ℕ, N < n → clean S n)
    (hFsub : (F : Set ℕ+) ⊆ S)
    (hFcomplete : ∀ s ∈ S, (s : ℕ) < t → s ∈ F)
    (hFbelow : ∀ s ∈ F, (s : ℕ) < t) :
  t ≤ N + 2 ^ F.card + 1 := by
  classical
  let rep : {n : ℕ // n ∈ Finset.Ico (N + 1) t} → Finset ℕ+ :=
    fun x => Classical.choose
      (ExistsUnique.exists (hclean x.1 (by
        have hx := x.2
        rw [Finset.mem_Ico] at hx
        omega)))
  have rep_spec (x : {n : ℕ // n ∈ Finset.Ico (N + 1) t}) :
      ((rep x : Set ℕ+) ⊆ S) ∧ Odd (rep x).card ∧
        (∑ s ∈ rep x, (s : ℕ) = x.1) := by
    exact Classical.choose_spec
      (ExistsUnique.exists (hclean x.1 (by
        have hx := x.2
        rw [Finset.mem_Ico] at hx
        omega)))
  have rep_mem (x : {n : ℕ // n ∈ Finset.Ico (N + 1) t}) :
      rep x ∈ F.powerset := by
    rw [Finset.mem_powerset]
    intro s hs
    have hsS : s ∈ S := rep_spec x |>.1 hs
    have hsle : (s : ℕ) ≤ x.1 := by
      calc
        (s : ℕ) ≤ ∑ a ∈ rep x, (a : ℕ) :=
          Finset.single_le_sum (fun a ha => Nat.zero_le _) hs
        _ = x.1 := (rep_spec x).2.2
    have hxt : x.1 < t := by
      have hx := x.2
      rw [Finset.mem_Ico] at hx
      exact hx.2
    exact hFcomplete s hsS (lt_of_le_of_lt hsle hxt)
  have hinj :
      Function.Injective
        (fun x : {n : ℕ // n ∈ Finset.Ico (N + 1) t} =>
          (⟨rep x, rep_mem x⟩ : {A : Finset ℕ+ // A ∈ F.powerset})) := by
    intro x y hxy
    apply Subtype.ext
    have hrep : rep x = rep y := congrArg Subtype.val hxy
    have hxsum := (rep_spec x).2.2
    have hysum := (rep_spec y).2.2
    have hval : x.1 = y.1 := by
      calc
        x.1 = ∑ s ∈ rep x, (s : ℕ) := hxsum.symm
        _ = ∑ s ∈ rep y, (s : ℕ) := by rw [hrep]
        _ = y.1 := hysum
    exact hval
  letI : Fintype {n : ℕ // n ∈ Finset.Ico (N + 1) t} :=
    Finset.Subtype.fintype (Finset.Ico (N + 1) t)
  have hcard :
      (Finset.Ico (N + 1) t).card ≤ F.powerset.card := by
    calc
      (Finset.Ico (N + 1) t).card =
          Fintype.card {n : ℕ // n ∈ Finset.Ico (N + 1) t} := by simp
      _ ≤ Fintype.card {A : Finset ℕ+ // A ∈ F.powerset} :=
        Fintype.card_le_of_injective _ hinj
      _ = F.powerset.card := by simp
  have hnum : t - (N + 1) ≤ 2 ^ F.card := by
    simpa using hcard
  omega
