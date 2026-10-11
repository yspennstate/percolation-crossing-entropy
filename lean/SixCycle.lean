import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The six-cycle coercivity inequality

A Lean 4 and Mathlib check of Lemma 7.2 and Proposition 7.3, the finite statements of
Section 7.2 ("A six-cycle coercivity inequality") of Yitzchak Shmalo,
*Entropy and singularity of spectral and pivotal sets in planar percolation*.

A configuration `z` of six signs and a subset `A` of `ℤ/6ℤ` are both encoded as numbers below `64`:
bit `i` of `z` is `1` when `z_i = +1`, and bit `i` of `A` is `1` when `i ∈ A`.
`L` is the set of configurations with at most two sign changes around the cycle, `I` the set of
independent subsets of the six-cycle, and `χ_A(z) = ∏_{i ∈ A} z_i`.

Writing `q = ∑_a u_a χ_{A_a}` over the eighteen independent sets, the uniform measure on the 64
configurations gives `‖q‖₂² = ∑ u_a²` (`orthonormal`) and `‖𝟙_L q‖₂² = (1/64) ∑_{z ∈ L} q(z)²`.
The main results are:
* `rank` (Lemma 7.2): a function in the span of `{χ_A : A ∈ I}` that vanishes on `L` is zero;
* `coercive`: `∑_{z ∈ L} q(z)² ≥ (32 - √848) ∑ u_a²`, that is `‖𝟙_L q‖₂² ≥ a_* ‖q‖₂²` with
  `a_* = (32 - √848)/64 = (8 - √53)/16` (`astar_eq`), and `sharp`: equality holds for a nonzero `q`;
* `coercivity` (Proposition 7.3): if `g` vanishes on `L`, then
  `∑_z (g z - Q g z)² ≥ a_* ∑_z g z²`, where `Q g = proj g` is the orthogonal projection onto the
  span of the eighteen characters (`proj_orth`);
* `coercivity_sharp` (Proposition 7.3, optimality): a nonzero `g` vanishing on `L` attains
  equality, so the constant `a_*` cannot be improved.
-/

namespace SixCycle

/-- bit `i` of `m` -/
def bit (m i : ℕ) : Bool := Nat.testBit m i

/-- the number of `i ∈ ℤ/6ℤ` with `z_i ≠ z_{i+1}` -/
def changes (z : ℕ) : ℕ := ((List.range 6).filter fun i => bit z i != bit z ((i + 1) % 6)).length

/-- `A` contains no two cyclically adjacent sites -/
def indep (A : ℕ) : Bool := (List.range 6).all fun i => !(bit A i && bit A ((i + 1) % 6))

/-- the number of elements of `A` -/
def size (A : ℕ) : ℕ := ((List.range 6).filter fun i => bit A i).length

/-- the Walsh character `χ_A(z) = ∏_{i ∈ A} z_i` -/
def chi (A z : ℕ) : ℤ :=
  ((List.range 6).filter fun i => bit A i).foldr (fun i acc => if bit z i then acc else -acc) 1

/-- configurations with at most two sign changes, listed in increasing order (`Lconf_spec`) -/
def Lconf : List ℕ := [0, 1, 2, 3, 4, 6, 7, 8, 12, 14, 15, 16, 24, 28, 30, 31, 32, 33, 35, 39, 47, 48, 49, 51, 55, 56, 57, 59, 60, 61, 62, 63]

theorem Lconf_spec : Lconf = (List.range 64).filter fun z => changes z ≤ 2 := by decide +kernel

/-- configurations with more than two sign changes -/
def Hconf : List ℕ := (List.range 64).filter fun z => 2 < changes z

/-- independent subsets of the six-cycle -/
def Iset : List ℕ := (List.range 64).filter indep

/-- the configuration whose plus signs form the cyclic interval of length `l` starting at `s` -/
def interval (s l : ℕ) : ℕ := ((List.range l).map fun k => 2 ^ ((s + k) % 6)).sum

/-- empty, full, and the thirty proper cyclic intervals of plus signs -/
def intervals : List ℕ :=
  [0, 63] ++ (List.range 6).flatMap fun s => (List.range 5).map fun l => interval s (l + 1)

theorem card_L : Lconf.length = 32 := by decide +kernel
theorem card_H : Hconf.length = 32 := by decide +kernel
theorem card_I : Iset.length = 18 := by decide +kernel

/-- the eighteen independent sets: the empty set, six singletons, nine pairs, two triples -/
theorem I_sizes :
    (Iset.filter fun A => size A = 0).length = 1 ∧ (Iset.filter fun A => size A = 1).length = 6 ∧
    (Iset.filter fun A => size A = 2).length = 9 ∧ (Iset.filter fun A => size A = 3).length = 2 := by
  decide +kernel

/-- `L` consists of the empty, the full, and the single-interval configurations -/
theorem L_intervals :
    intervals.length = 32 ∧ intervals.Nodup ∧ ∀ z ∈ intervals, z ∈ Lconf := by decide +kernel

/-- the order used below: the empty set, the six pairs `{i, i+2}`, the three pairs `{i, i+3}`,
the six singletons, and the two alternating triples -/
def basis : List ℕ := [0, 5, 10, 20, 40, 17, 34, 9, 18, 36, 1, 2, 4, 8, 16, 32, 21, 42]

theorem basis_spec : basis.length = 18 ∧ basis.Nodup ∧ ∀ A ∈ basis, A ∈ Iset := by decide +kernel

/-- `Mtab j a = χ_{A_a}(z_j)`, for the configurations `z_j` of `L` and the sets `A_a` of `basis` -/
def Mtab : Fin 32 → Fin 18 → ℤ :=
  ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1],
    ![1, -1, 1, 1, 1, -1, 1, -1, 1, 1, 1, -1, -1, -1, -1, -1, 1, -1],
    ![1, 1, -1, 1, 1, 1, -1, 1, -1, 1, -1, 1, -1, -1, -1, -1, -1, 1],
    ![1, -1, -1, 1, 1, -1, -1, -1, -1, 1, 1, 1, -1, -1, -1, -1, 1, 1],
    ![1, -1, 1, -1, 1, 1, 1, 1, 1, -1, -1, -1, 1, -1, -1, -1, 1, -1],
    ![1, -1, -1, -1, 1, 1, -1, 1, -1, -1, -1, 1, 1, -1, -1, -1, 1, 1],
    ![1, 1, -1, -1, 1, -1, -1, -1, -1, -1, 1, 1, 1, -1, -1, -1, -1, 1],
    ![1, 1, -1, 1, -1, 1, 1, -1, 1, 1, -1, -1, -1, 1, -1, -1, -1, 1],
    ![1, -1, -1, -1, -1, 1, 1, -1, 1, -1, -1, -1, 1, 1, -1, -1, 1, 1],
    ![1, -1, 1, -1, -1, 1, -1, -1, -1, -1, -1, 1, 1, 1, -1, -1, 1, -1],
    ![1, 1, 1, -1, -1, -1, -1, 1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1],
    ![1, 1, 1, -1, 1, -1, 1, 1, -1, 1, -1, -1, -1, -1, 1, -1, 1, -1],
    ![1, 1, -1, -1, -1, -1, 1, -1, -1, 1, -1, -1, -1, 1, 1, -1, 1, 1],
    ![1, -1, -1, 1, -1, -1, 1, -1, -1, -1, -1, -1, 1, 1, 1, -1, -1, 1],
    ![1, -1, 1, 1, -1, -1, -1, -1, 1, -1, -1, 1, 1, 1, 1, -1, -1, -1],
    ![1, 1, 1, 1, -1, 1, -1, 1, 1, -1, 1, 1, 1, 1, 1, -1, 1, -1],
    ![1, 1, 1, 1, -1, 1, -1, 1, 1, -1, -1, -1, -1, -1, -1, 1, -1, 1],
    ![1, -1, 1, 1, -1, -1, -1, -1, 1, -1, 1, -1, -1, -1, -1, 1, 1, 1],
    ![1, -1, -1, 1, -1, -1, 1, -1, -1, -1, 1, 1, -1, -1, -1, 1, 1, -1],
    ![1, 1, -1, -1, -1, -1, 1, -1, -1, 1, 1, 1, 1, -1, -1, 1, -1, -1],
    ![1, 1, 1, -1, 1, -1, 1, 1, -1, 1, 1, 1, 1, 1, -1, 1, -1, 1],
    ![1, 1, 1, -1, -1, -1, -1, 1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1],
    ![1, -1, 1, -1, -1, 1, -1, -1, -1, -1, 1, -1, -1, -1, 1, 1, -1, 1],
    ![1, -1, -1, -1, -1, 1, 1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, -1],
    ![1, 1, -1, 1, -1, 1, 1, -1, 1, 1, 1, 1, 1, -1, 1, 1, 1, -1],
    ![1, 1, -1, -1, 1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, -1],
    ![1, -1, -1, -1, 1, 1, -1, 1, -1, -1, 1, -1, -1, 1, 1, 1, -1, -1],
    ![1, -1, 1, -1, 1, 1, 1, 1, 1, -1, 1, 1, -1, 1, 1, 1, -1, 1],
    ![1, -1, -1, 1, 1, -1, -1, -1, -1, 1, -1, -1, 1, 1, 1, 1, -1, -1],
    ![1, 1, -1, 1, 1, 1, -1, 1, -1, 1, 1, -1, 1, 1, 1, 1, 1, -1],
    ![1, -1, 1, 1, 1, -1, 1, -1, 1, 1, -1, 1, 1, 1, 1, 1, -1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]

theorem Mtab_spec : ∀ j : Fin 32, ∀ a : Fin 18,
    chi (basis.getD a.val 0) (Lconf.getD j.val 0) = Mtab j a := by decide +kernel

/-- on all 64 configurations the eighteen characters are orthogonal with norm `64` -/
theorem orthonormal : (List.range 18).all (fun a => (List.range 18).all fun b =>
    ((List.range 64).map fun z => chi (basis.getD a 0) z * chi (basis.getD b 0) z).sum ==
      if a = b then 64 else 0) = true := by
  decide +kernel

/-- `∑_{z ∈ L} q(z)²` for `q = ∑_a u_a χ_{A_a}` -/
def massL (u : Fin 18 → ℝ) : ℝ := ∑ j : Fin 32, (∑ a : Fin 18, (Mtab j a : ℝ) * u a) ^ 2

set_option maxHeartbeats 4000000 in
theorem massL_eq (u : Fin 18 → ℝ) : massL u = 32 * u 0 ^ 2 - 8 * u 0 * u 7 - 8 * u 0 * u 8 - 8 * u 0 * u 9 + 32 * u 1 ^ 2 + 24 * u 1 * u 7 - 8 * u 1 * u 8 + 24 * u 1 * u 9 + 32 * u 2 ^ 2 + 24 * u 2 * u 7 + 24 * u 2 * u 8 - 8 * u 2 * u 9 + 32 * u 3 ^ 2 - 8 * u 3 * u 7 + 24 * u 3 * u 8 + 24 * u 3 * u 9 + 32 * u 4 ^ 2 + 24 * u 4 * u 7 - 8 * u 4 * u 8 + 24 * u 4 * u 9 + 32 * u 5 ^ 2 + 24 * u 5 * u 7 + 24 * u 5 * u 8 - 8 * u 5 * u 9 + 32 * u 6 ^ 2 - 8 * u 6 * u 7 + 24 * u 6 * u 8 + 24 * u 6 * u 9 + 32 * u 7 ^ 2 + 32 * u 8 ^ 2 + 32 * u 9 ^ 2 + 32 * u 10 ^ 2 + 24 * u 10 * u 11 - 8 * u 10 * u 13 + 24 * u 10 * u 15 - 8 * u 10 * u 17 + 32 * u 11 ^ 2 + 24 * u 11 * u 12 - 8 * u 11 * u 14 - 8 * u 11 * u 16 + 32 * u 12 ^ 2 + 24 * u 12 * u 13 - 8 * u 12 * u 15 - 8 * u 12 * u 17 + 32 * u 13 ^ 2 + 24 * u 13 * u 14 - 8 * u 13 * u 16 + 32 * u 14 ^ 2 + 24 * u 14 * u 15 - 8 * u 14 * u 17 + 32 * u 15 ^ 2 - 8 * u 15 * u 16 + 32 * u 16 ^ 2 - 8 * u 16 * u 17 + 32 * u 17 ^ 2 := by
  simp [massL, Fin.sum_univ_succ, Mtab]
  ring

theorem sumsq_eq (u : Fin 18 → ℝ) : ∑ a : Fin 18, u a ^ 2 = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 + u 4 ^ 2 + u 5 ^ 2 + u 6 ^ 2 + u 7 ^ 2 + u 8 ^ 2 + u 9 ^ 2 + u 10 ^ 2 + u 11 ^ 2 + u 12 ^ 2 + u 13 ^ 2 + u 14 ^ 2 + u 15 ^ 2 + u 16 ^ 2 + u 17 ^ 2 := by
  simp [Fin.sum_univ_succ]
  ring

set_option maxHeartbeats 4000000 in
/-- the coercivity bound `∑_{z ∈ L} q(z)² ≥ (32 - √848) ∑ u_a²` -/
theorem coercive (u : Fin 18 → ℝ) : (32 - Real.sqrt 848) * ∑ a, u a ^ 2 ≤ massL u := by
  rw [massL_eq, sumsq_eq]
  set s := Real.sqrt 848 with hs_def
  have hs : s ^ 2 = 848 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have h29 : 29 ≤ s := by nlinarith
  have hpos : 0 < s := by linarith
  have key : s * ((32 * u 0 ^ 2 - 8 * u 0 * u 7 - 8 * u 0 * u 8 - 8 * u 0 * u 9 + 32 * u 1 ^ 2 + 24 * u 1 * u 7 - 8 * u 1 * u 8 + 24 * u 1 * u 9 + 32 * u 2 ^ 2 + 24 * u 2 * u 7 + 24 * u 2 * u 8 - 8 * u 2 * u 9 + 32 * u 3 ^ 2 - 8 * u 3 * u 7 + 24 * u 3 * u 8 + 24 * u 3 * u 9 + 32 * u 4 ^ 2 + 24 * u 4 * u 7 - 8 * u 4 * u 8 + 24 * u 4 * u 9 + 32 * u 5 ^ 2 + 24 * u 5 * u 7 + 24 * u 5 * u 8 - 8 * u 5 * u 9 + 32 * u 6 ^ 2 - 8 * u 6 * u 7 + 24 * u 6 * u 8 + 24 * u 6 * u 9 + 32 * u 7 ^ 2 + 32 * u 8 ^ 2 + 32 * u 9 ^ 2 + 32 * u 10 ^ 2 + 24 * u 10 * u 11 - 8 * u 10 * u 13 + 24 * u 10 * u 15 - 8 * u 10 * u 17 + 32 * u 11 ^ 2 + 24 * u 11 * u 12 - 8 * u 11 * u 14 - 8 * u 11 * u 16 + 32 * u 12 ^ 2 + 24 * u 12 * u 13 - 8 * u 12 * u 15 - 8 * u 12 * u 17 + 32 * u 13 ^ 2 + 24 * u 13 * u 14 - 8 * u 13 * u 16 + 32 * u 14 ^ 2 + 24 * u 14 * u 15 - 8 * u 14 * u 17 + 32 * u 15 ^ 2 - 8 * u 15 * u 16 + 32 * u 16 ^ 2 - 8 * u 16 * u 17 + 32 * u 17 ^ 2) - (32 - s) * (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 + u 4 ^ 2 + u 5 ^ 2 + u 6 ^ 2 + u 7 ^ 2 + u 8 ^ 2 + u 9 ^ 2 + u 10 ^ 2 + u 11 ^ 2 + u 12 ^ 2 + u 13 ^ 2 + u 14 ^ 2 + u 15 ^ 2 + u 16 ^ 2 + u 17 ^ 2)) =
      ((s * u 0 + - 4 * u 7 - 4 * u 8 - 4 * u 9) ^ 2 + (s * u 1 + 12 * u 7 - 4 * u 8 + 12 * u 9) ^ 2 + (s * u 2 + 12 * u 7 + 12 * u 8 - 4 * u 9) ^ 2 + (s * u 3 + - 4 * u 7 + 12 * u 8 + 12 * u 9) ^ 2 + (s * u 4 + 12 * u 7 - 4 * u 8 + 12 * u 9) ^ 2 + (s * u 5 + 12 * u 7 + 12 * u 8 - 4 * u 9) ^ 2 + (s * u 6 + - 4 * u 7 + 12 * u 8 + 12 * u 9) ^ 2 + 112 * ((u 7 - u 8) ^ 2 + (u 7 - u 9) ^ 2 + (u 8 - u 9) ^ 2)) + s * (29 * (u 10 + (12 / 29) * u 11 - (4 / 29) * u 13 + (12 / 29) * u 15 - (4 / 29) * u 17) ^ 2 + (697 / 29) * (u 11 + (348 / 697) * u 12 + (48 / 697) * u 13 - (116 / 697) * u 14 - (144 / 697) * u 15 - (116 / 697) * u 16 + (48 / 697) * u 17) ^ 2 + (16037 / 697) * (u 12 + (7788 / 16037) * u 13 + (48 / 553) * u 14 - (1060 / 16037) * u 15 + (48 / 553) * u 16 - (116 / 553) * u 17) ^ 2 + (367377 / 16037) * (u 13 + (60436 / 122459) * u 14 + (14624 / 122459) * u 15 - (75284 / 367377) * u 16 + (26912 / 367377) * u 17) ^ 2 + (2765295 / 122459) * (u 14 + (2084 / 4727) * u 15 + (32 / 489) * u 16 - (2596 / 14181) * u 17) ^ 2 + (85995 / 4727) * (u 15 - (116 / 441) * u 16 + (80 / 441) * u 17) ^ 2 + (3799 / 147) * (u 16 - (268 / 3799) * u 17) ^ 2 + (97691 / 3799) * (u 17) ^ 2) + s * (s - 29) * (u 10 ^ 2 + u 11 ^ 2 + u 12 ^ 2 + u 13 ^ 2 + u 14 ^ 2 + u 15 ^ 2 + u 16 ^ 2 + u 17 ^ 2) := by
    linear_combination (u 7 ^ 2 + u 8 ^ 2 + u 9 ^ 2) * hs
  have hA : 0 ≤ (s * u 0 + - 4 * u 7 - 4 * u 8 - 4 * u 9) ^ 2 + (s * u 1 + 12 * u 7 - 4 * u 8 + 12 * u 9) ^ 2 + (s * u 2 + 12 * u 7 + 12 * u 8 - 4 * u 9) ^ 2 + (s * u 3 + - 4 * u 7 + 12 * u 8 + 12 * u 9) ^ 2 + (s * u 4 + 12 * u 7 - 4 * u 8 + 12 * u 9) ^ 2 + (s * u 5 + 12 * u 7 + 12 * u 8 - 4 * u 9) ^ 2 + (s * u 6 + - 4 * u 7 + 12 * u 8 + 12 * u 9) ^ 2 + 112 * ((u 7 - u 8) ^ 2 + (u 7 - u 9) ^ 2 + (u 8 - u 9) ^ 2) := by positivity
  have hB : 0 ≤ 29 * (u 10 + (12 / 29) * u 11 - (4 / 29) * u 13 + (12 / 29) * u 15 - (4 / 29) * u 17) ^ 2 + (697 / 29) * (u 11 + (348 / 697) * u 12 + (48 / 697) * u 13 - (116 / 697) * u 14 - (144 / 697) * u 15 - (116 / 697) * u 16 + (48 / 697) * u 17) ^ 2 + (16037 / 697) * (u 12 + (7788 / 16037) * u 13 + (48 / 553) * u 14 - (1060 / 16037) * u 15 + (48 / 553) * u 16 - (116 / 553) * u 17) ^ 2 + (367377 / 16037) * (u 13 + (60436 / 122459) * u 14 + (14624 / 122459) * u 15 - (75284 / 367377) * u 16 + (26912 / 367377) * u 17) ^ 2 + (2765295 / 122459) * (u 14 + (2084 / 4727) * u 15 + (32 / 489) * u 16 - (2596 / 14181) * u 17) ^ 2 + (85995 / 4727) * (u 15 - (116 / 441) * u 16 + (80 / 441) * u 17) ^ 2 + (3799 / 147) * (u 16 - (268 / 3799) * u 17) ^ 2 + (97691 / 3799) * (u 17) ^ 2 := by positivity
  have hC : 0 ≤ u 10 ^ 2 + u 11 ^ 2 + u 12 ^ 2 + u 13 ^ 2 + u 14 ^ 2 + u 15 ^ 2 + u 16 ^ 2 + u 17 ^ 2 := by positivity
  have h1 : 0 ≤ s * ((32 * u 0 ^ 2 - 8 * u 0 * u 7 - 8 * u 0 * u 8 - 8 * u 0 * u 9 + 32 * u 1 ^ 2 + 24 * u 1 * u 7 - 8 * u 1 * u 8 + 24 * u 1 * u 9 + 32 * u 2 ^ 2 + 24 * u 2 * u 7 + 24 * u 2 * u 8 - 8 * u 2 * u 9 + 32 * u 3 ^ 2 - 8 * u 3 * u 7 + 24 * u 3 * u 8 + 24 * u 3 * u 9 + 32 * u 4 ^ 2 + 24 * u 4 * u 7 - 8 * u 4 * u 8 + 24 * u 4 * u 9 + 32 * u 5 ^ 2 + 24 * u 5 * u 7 + 24 * u 5 * u 8 - 8 * u 5 * u 9 + 32 * u 6 ^ 2 - 8 * u 6 * u 7 + 24 * u 6 * u 8 + 24 * u 6 * u 9 + 32 * u 7 ^ 2 + 32 * u 8 ^ 2 + 32 * u 9 ^ 2 + 32 * u 10 ^ 2 + 24 * u 10 * u 11 - 8 * u 10 * u 13 + 24 * u 10 * u 15 - 8 * u 10 * u 17 + 32 * u 11 ^ 2 + 24 * u 11 * u 12 - 8 * u 11 * u 14 - 8 * u 11 * u 16 + 32 * u 12 ^ 2 + 24 * u 12 * u 13 - 8 * u 12 * u 15 - 8 * u 12 * u 17 + 32 * u 13 ^ 2 + 24 * u 13 * u 14 - 8 * u 13 * u 16 + 32 * u 14 ^ 2 + 24 * u 14 * u 15 - 8 * u 14 * u 17 + 32 * u 15 ^ 2 - 8 * u 15 * u 16 + 32 * u 16 ^ 2 - 8 * u 16 * u 17 + 32 * u 17 ^ 2) - (32 - s) * (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 + u 4 ^ 2 + u 5 ^ 2 + u 6 ^ 2 + u 7 ^ 2 + u 8 ^ 2 + u 9 ^ 2 + u 10 ^ 2 + u 11 ^ 2 + u 12 ^ 2 + u 13 ^ 2 + u 14 ^ 2 + u 15 ^ 2 + u 16 ^ 2 + u 17 ^ 2)) := by
    rw [key]
    have := mul_nonneg hs0 hB
    have := mul_nonneg (mul_nonneg hs0 (sub_nonneg.mpr h29)) hC
    linarith
  have h2 := (mul_nonneg_iff_of_pos_left hpos).mp h1
  linarith

set_option maxHeartbeats 4000000 in
/-- the constant is attained: `(32 - √848)` is the least eigenvalue of the Gram matrix -/
theorem sharp : ∃ u : Fin 18 → ℝ, u ≠ 0 ∧ massL u = (32 - Real.sqrt 848) * ∑ a, u a ^ 2 := by
  set s := Real.sqrt 848 with hs_def
  have hs : s ^ 2 = 848 := Real.sq_sqrt (by norm_num)
  refine ⟨![(3 / 212) * s, (-5 / 212) * s, (-5 / 212) * s, (-5 / 212) * s, (-5 / 212) * s, (-5 / 212) * s, (-5 / 212) * s, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ?_, ?_⟩
  · intro h
    have := congrFun h 7
    simp at this
  · rw [massL_eq, sumsq_eq]
    simp only [Matrix.cons_val, Matrix.cons_val_zero]
    linear_combination (3 * s / 848) * hs

/-- a combination of the eighteen characters that vanishes on `L` is zero -/
theorem rank (u : Fin 18 → ℝ) (h : ∀ j : Fin 32, ∑ a : Fin 18, (Mtab j a : ℝ) * u a = 0) : u = 0 := by
  have hc := coercive u
  have h0 : massL u = 0 := by simp [massL, h]
  rw [h0] at hc
  have hs : Real.sqrt 848 ^ 2 = 848 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 848 := Real.sqrt_nonneg _
  have hlt : 0 < 32 - Real.sqrt 848 := by nlinarith
  have hsum : ∑ a, u a ^ 2 = 0 := by
    have := Finset.sum_nonneg (fun a (_ : a ∈ Finset.univ) => sq_nonneg (u a))
    nlinarith
  funext a
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (u i))).mp hsum a (Finset.mem_univ a)
  simpa using this

theorem sqrt848 : Real.sqrt 848 = 4 * Real.sqrt 53 := by
  rw [show (848 : ℝ) = 4 ^ 2 * 53 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

/-- `a_* = (32 - √848)/64 = (8 - √53)/16` -/
theorem astar_eq : (32 - Real.sqrt 848) / 64 = (8 - Real.sqrt 53) / 16 := by
  rw [sqrt848]; ring

theorem astar_gt : (1 : ℝ) / 32 < (8 - Real.sqrt 53) / 16 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 53 by norm_num)
  have h0 := Real.sqrt_nonneg (53 : ℝ)
  nlinarith

/-! ## The proposition

A function `g` of six signs is a vector `g : Fin 64 → ℝ`. Sums over the 64 configurations are `64`
times the norms of the uniform measure, which changes neither side of the inequality. -/

/-- `Xtab z a = χ_{A_a}(z)` for every configuration `z` (`Xtab_spec`) -/
def Xtab : Fin 64 → Fin 18 → ℤ :=
  ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1],
    ![1, -1, 1, 1, 1, -1, 1, -1, 1, 1, 1, -1, -1, -1, -1, -1, 1, -1],
    ![1, 1, -1, 1, 1, 1, -1, 1, -1, 1, -1, 1, -1, -1, -1, -1, -1, 1],
    ![1, -1, -1, 1, 1, -1, -1, -1, -1, 1, 1, 1, -1, -1, -1, -1, 1, 1],
    ![1, -1, 1, -1, 1, 1, 1, 1, 1, -1, -1, -1, 1, -1, -1, -1, 1, -1],
    ![1, 1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, -1, -1, -1, -1],
    ![1, -1, -1, -1, 1, 1, -1, 1, -1, -1, -1, 1, 1, -1, -1, -1, 1, 1],
    ![1, 1, -1, -1, 1, -1, -1, -1, -1, -1, 1, 1, 1, -1, -1, -1, -1, 1],
    ![1, 1, -1, 1, -1, 1, 1, -1, 1, 1, -1, -1, -1, 1, -1, -1, -1, 1],
    ![1, -1, -1, 1, -1, -1, 1, 1, 1, 1, 1, -1, -1, 1, -1, -1, 1, 1],
    ![1, 1, 1, 1, -1, 1, -1, -1, -1, 1, -1, 1, -1, 1, -1, -1, -1, -1],
    ![1, -1, 1, 1, -1, -1, -1, 1, -1, 1, 1, 1, -1, 1, -1, -1, 1, -1],
    ![1, -1, -1, -1, -1, 1, 1, -1, 1, -1, -1, -1, 1, 1, -1, -1, 1, 1],
    ![1, 1, -1, -1, -1, -1, 1, 1, 1, -1, 1, -1, 1, 1, -1, -1, -1, 1],
    ![1, -1, 1, -1, -1, 1, -1, -1, -1, -1, -1, 1, 1, 1, -1, -1, 1, -1],
    ![1, 1, 1, -1, -1, -1, -1, 1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1],
    ![1, 1, 1, -1, 1, -1, 1, 1, -1, 1, -1, -1, -1, -1, 1, -1, 1, -1],
    ![1, -1, 1, -1, 1, 1, 1, -1, -1, 1, 1, -1, -1, -1, 1, -1, -1, -1],
    ![1, 1, -1, -1, 1, -1, -1, 1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1],
    ![1, -1, -1, -1, 1, 1, -1, -1, 1, 1, 1, 1, -1, -1, 1, -1, -1, 1],
    ![1, -1, 1, 1, 1, -1, 1, 1, -1, -1, -1, -1, 1, -1, 1, -1, -1, -1],
    ![1, 1, 1, 1, 1, 1, 1, -1, -1, -1, 1, -1, 1, -1, 1, -1, 1, -1],
    ![1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1],
    ![1, 1, -1, 1, 1, 1, -1, -1, 1, -1, 1, 1, 1, -1, 1, -1, 1, 1],
    ![1, 1, -1, -1, -1, -1, 1, -1, -1, 1, -1, -1, -1, 1, 1, -1, 1, 1],
    ![1, -1, -1, -1, -1, 1, 1, 1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1],
    ![1, 1, 1, -1, -1, -1, -1, -1, 1, 1, -1, 1, -1, 1, 1, -1, 1, -1],
    ![1, -1, 1, -1, -1, 1, -1, 1, 1, 1, 1, 1, -1, 1, 1, -1, -1, -1],
    ![1, -1, -1, 1, -1, -1, 1, -1, -1, -1, -1, -1, 1, 1, 1, -1, -1, 1],
    ![1, 1, -1, 1, -1, 1, 1, 1, -1, -1, 1, -1, 1, 1, 1, -1, 1, 1],
    ![1, -1, 1, 1, -1, -1, -1, -1, 1, -1, -1, 1, 1, 1, 1, -1, -1, -1],
    ![1, 1, 1, 1, -1, 1, -1, 1, 1, -1, 1, 1, 1, 1, 1, -1, 1, -1],
    ![1, 1, 1, 1, -1, 1, -1, 1, 1, -1, -1, -1, -1, -1, -1, 1, -1, 1],
    ![1, -1, 1, 1, -1, -1, -1, -1, 1, -1, 1, -1, -1, -1, -1, 1, 1, 1],
    ![1, 1, -1, 1, -1, 1, 1, 1, -1, -1, -1, 1, -1, -1, -1, 1, -1, -1],
    ![1, -1, -1, 1, -1, -1, 1, -1, -1, -1, 1, 1, -1, -1, -1, 1, 1, -1],
    ![1, -1, 1, -1, -1, 1, -1, 1, 1, 1, -1, -1, 1, -1, -1, 1, 1, 1],
    ![1, 1, 1, -1, -1, -1, -1, -1, 1, 1, 1, -1, 1, -1, -1, 1, -1, 1],
    ![1, -1, -1, -1, -1, 1, 1, 1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1],
    ![1, 1, -1, -1, -1, -1, 1, -1, -1, 1, 1, 1, 1, -1, -1, 1, -1, -1],
    ![1, 1, -1, 1, 1, 1, -1, -1, 1, -1, -1, -1, -1, 1, -1, 1, -1, -1],
    ![1, -1, -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1],
    ![1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, 1, -1, 1, -1, 1, -1, 1],
    ![1, -1, 1, 1, 1, -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, 1, 1, 1],
    ![1, -1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, 1, 1, -1],
    ![1, 1, -1, -1, 1, -1, -1, 1, 1, 1, 1, -1, 1, 1, -1, 1, -1, -1],
    ![1, -1, 1, -1, 1, 1, 1, -1, -1, 1, -1, 1, 1, 1, -1, 1, 1, 1],
    ![1, 1, 1, -1, 1, -1, 1, 1, -1, 1, 1, 1, 1, 1, -1, 1, -1, 1],
    ![1, 1, 1, -1, -1, -1, -1, 1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1],
    ![1, -1, 1, -1, -1, 1, -1, -1, -1, -1, 1, -1, -1, -1, 1, 1, -1, 1],
    ![1, 1, -1, -1, -1, -1, 1, 1, 1, -1, -1, 1, -1, -1, 1, 1, 1, -1],
    ![1, -1, -1, -1, -1, 1, 1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, -1],
    ![1, -1, 1, 1, -1, -1, -1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1],
    ![1, 1, 1, 1, -1, 1, -1, -1, -1, 1, 1, -1, 1, -1, 1, 1, 1, 1],
    ![1, -1, -1, 1, -1, -1, 1, 1, 1, 1, -1, 1, 1, -1, 1, 1, -1, -1],
    ![1, 1, -1, 1, -1, 1, 1, -1, 1, 1, 1, 1, 1, -1, 1, 1, 1, -1],
    ![1, 1, -1, -1, 1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, -1],
    ![1, -1, -1, -1, 1, 1, -1, 1, -1, -1, 1, -1, -1, 1, 1, 1, -1, -1],
    ![1, 1, 1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1, 1, 1, 1, 1, 1],
    ![1, -1, 1, -1, 1, 1, 1, 1, 1, -1, 1, 1, -1, 1, 1, 1, -1, 1],
    ![1, -1, -1, 1, 1, -1, -1, -1, -1, 1, -1, -1, 1, 1, 1, 1, -1, -1],
    ![1, 1, -1, 1, 1, 1, -1, 1, -1, 1, 1, -1, 1, 1, 1, 1, 1, -1],
    ![1, -1, 1, 1, 1, -1, 1, -1, 1, 1, -1, 1, 1, 1, 1, 1, -1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]

theorem Xtab_spec : ∀ z : Fin 64, ∀ a : Fin 18, chi (basis.getD a.val 0) z.val = Xtab z a := by
  decide +kernel

/-- the indicator of `L` (`Ltab_spec`) -/
def Ltab : Fin 64 → ℤ := ![1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1]

theorem Ltab_spec : ∀ z : Fin 64,
    (changes z.val ≤ 2 → Ltab z = 1) ∧ (¬ changes z.val ≤ 2 → Ltab z = 0) := by
  decide +kernel

/-- the eighteen characters are orthogonal on the 64 configurations, with squared norm `64` -/
theorem Xorth : ∀ a b : Fin 18, ∑ z : Fin 64, Xtab z a * Xtab z b = if a = b then 64 else 0 := by
  decide +kernel

theorem Xorth_real (a b : Fin 18) :
    ∑ z : Fin 64, (Xtab z a : ℝ) * (Xtab z b : ℝ) = if a = b then 64 else 0 := by
  have h := Xorth a b
  split_ifs at h ⊢ <;> exact_mod_cast h

/-- the Walsh coefficient `⟨g, χ_{A_a}⟩` for the uniform measure -/
noncomputable def coef (g : Fin 64 → ℝ) (a : Fin 18) : ℝ :=
  (∑ z : Fin 64, g z * (Xtab z a : ℝ)) / 64

/-- `Q g = ∑_a ⟨g, χ_{A_a}⟩ χ_{A_a}`; by `proj_orth` it is the orthogonal projection -/
noncomputable def proj (g : Fin 64 → ℝ) (z : Fin 64) : ℝ :=
  ∑ a : Fin 18, coef g a * (Xtab z a : ℝ)

/-- the combination `∑_a u_a χ_{A_a}` has Walsh coefficients `u` -/
theorem pair_comb (u : Fin 18 → ℝ) (b : Fin 18) :
    ∑ z : Fin 64, (∑ a : Fin 18, u a * (Xtab z a : ℝ)) * (Xtab z b : ℝ) = 64 * u b := by
  calc ∑ z : Fin 64, (∑ a : Fin 18, u a * (Xtab z a : ℝ)) * (Xtab z b : ℝ)
      = ∑ z : Fin 64, ∑ a : Fin 18, u a * ((Xtab z a : ℝ) * (Xtab z b : ℝ)) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        ring
    _ = ∑ a : Fin 18, u a * ∑ z : Fin 64, (Xtab z a : ℝ) * (Xtab z b : ℝ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ a : Fin 18, u a * (if a = b then 64 else 0) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Xorth_real]
    _ = 64 * u b := by
        rw [Finset.sum_eq_single b]
        · rw [if_pos rfl]; ring
        · intro a _ hab; rw [if_neg hab, mul_zero]
        · intro h; exact absurd (Finset.mem_univ b) h

/-- `g - Q g` is orthogonal to every character, so `proj` is the orthogonal projection `Q` -/
theorem proj_orth (g : Fin 64 → ℝ) (b : Fin 18) :
    ∑ z : Fin 64, (g z - proj g z) * (Xtab z b : ℝ) = 0 := by
  have h1 : ∑ z : Fin 64, proj g z * (Xtab z b : ℝ) = 64 * coef g b := pair_comb (coef g) b
  have h2 : ∑ z : Fin 64, g z * (Xtab z b : ℝ) = 64 * coef g b := by
    unfold coef; ring
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [h1, h2, sub_self]

/-- `∑_z q(z)² = 64 ∑_a u_a²` for `q = ∑_a u_a χ_{A_a}` -/
theorem total (u : Fin 18 → ℝ) :
    ∑ z : Fin 64, (∑ a : Fin 18, u a * (Xtab z a : ℝ)) ^ 2 = 64 * ∑ a : Fin 18, u a ^ 2 := by
  calc ∑ z : Fin 64, (∑ a : Fin 18, u a * (Xtab z a : ℝ)) ^ 2
      = ∑ z : Fin 64, ∑ b : Fin 18,
          u b * ((∑ a : Fin 18, u a * (Xtab z a : ℝ)) * (Xtab z b : ℝ)) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [sq, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring
    _ = ∑ b : Fin 18, u b * ∑ z : Fin 64,
          (∑ a : Fin 18, u a * (Xtab z a : ℝ)) * (Xtab z b : ℝ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ b : Fin 18, u b * (64 * u b) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [pair_comb]
    _ = 64 * ∑ a : Fin 18, u a ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring

/-- `∑_{z ∈ L} q(z)²`, written over all 64 configurations -/
def massAll (u : Fin 18 → ℝ) : ℝ :=
  ∑ z : Fin 64, (Ltab z : ℝ) * (∑ a : Fin 18, u a * (Xtab z a : ℝ)) ^ 2

set_option maxHeartbeats 4000000 in
theorem massAll_eq (u : Fin 18 → ℝ) : massAll u = 32 * u 0 ^ 2 - 8 * u 0 * u 7 - 8 * u 0 * u 8 - 8 * u 0 * u 9 + 32 * u 1 ^ 2 + 24 * u 1 * u 7 - 8 * u 1 * u 8 + 24 * u 1 * u 9 + 32 * u 2 ^ 2 + 24 * u 2 * u 7 + 24 * u 2 * u 8 - 8 * u 2 * u 9 + 32 * u 3 ^ 2 - 8 * u 3 * u 7 + 24 * u 3 * u 8 + 24 * u 3 * u 9 + 32 * u 4 ^ 2 + 24 * u 4 * u 7 - 8 * u 4 * u 8 + 24 * u 4 * u 9 + 32 * u 5 ^ 2 + 24 * u 5 * u 7 + 24 * u 5 * u 8 - 8 * u 5 * u 9 + 32 * u 6 ^ 2 - 8 * u 6 * u 7 + 24 * u 6 * u 8 + 24 * u 6 * u 9 + 32 * u 7 ^ 2 + 32 * u 8 ^ 2 + 32 * u 9 ^ 2 + 32 * u 10 ^ 2 + 24 * u 10 * u 11 - 8 * u 10 * u 13 + 24 * u 10 * u 15 - 8 * u 10 * u 17 + 32 * u 11 ^ 2 + 24 * u 11 * u 12 - 8 * u 11 * u 14 - 8 * u 11 * u 16 + 32 * u 12 ^ 2 + 24 * u 12 * u 13 - 8 * u 12 * u 15 - 8 * u 12 * u 17 + 32 * u 13 ^ 2 + 24 * u 13 * u 14 - 8 * u 13 * u 16 + 32 * u 14 ^ 2 + 24 * u 14 * u 15 - 8 * u 14 * u 17 + 32 * u 15 ^ 2 - 8 * u 15 * u 16 + 32 * u 16 ^ 2 - 8 * u 16 * u 17 + 32 * u 17 ^ 2 := by
  simp [massAll, Fin.sum_univ_succ, Xtab, Ltab]
  ring

theorem massAll_massL (u : Fin 18 → ℝ) : massAll u = massL u := by
  rw [massAll_eq, massL_eq]

set_option maxHeartbeats 4000000 in
/-- **The proposition.** If `g` vanishes on `L`, then `‖(Id - Q) g‖² ≥ a_* ‖g‖²`,
with `a_* = (32 - √848)/64` -/
theorem coercivity (g : Fin 64 → ℝ) (hg : ∀ z : Fin 64, changes z.val ≤ 2 → g z = 0) :
    (32 - Real.sqrt 848) / 64 * ∑ z : Fin 64, g z ^ 2 ≤ ∑ z : Fin 64, (g z - proj g z) ^ 2 := by
  have hs0 : 0 ≤ Real.sqrt 848 := Real.sqrt_nonneg _
  have hq : ∀ z, proj g z = ∑ a : Fin 18, coef g a * (Xtab z a : ℝ) := fun z => rfl
  have hQQ : ∑ z : Fin 64, proj g z ^ 2 = 64 * ∑ a, coef g a ^ 2 := total (coef g)
  have h2 : ∀ a, ∑ z : Fin 64, g z * (Xtab z a : ℝ) = 64 * coef g a := by
    intro a; unfold coef; ring
  have hgQ : ∑ z : Fin 64, g z * proj g z = 64 * ∑ a, coef g a ^ 2 := by
    calc ∑ z : Fin 64, g z * proj g z
        = ∑ z : Fin 64, ∑ a : Fin 18, coef g a * (g z * (Xtab z a : ℝ)) := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [hq, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          ring
      _ = ∑ a : Fin 18, coef g a * ∑ z : Fin 64, g z * (Xtab z a : ℝ) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
      _ = 64 * ∑ a, coef g a ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [h2]; ring
  -- `𝟙_H Q g` agrees with `Q g` wherever `g` is not zero
  have hgr : ∀ z, g z * proj g z = g z * ((1 - (Ltab z : ℝ)) * proj g z) := by
    intro z
    by_cases h : changes z.val ≤ 2
    · rw [hg z h]; ring
    · have h0 : (Ltab z : ℝ) = 0 := by exact_mod_cast (Ltab_spec z).2 h
      rw [h0]; ring
  have hr2 : ∀ z, ((1 - (Ltab z : ℝ)) * proj g z) ^ 2
      = proj g z ^ 2 - (Ltab z : ℝ) * proj g z ^ 2 := by
    intro z
    by_cases h : changes z.val ≤ 2
    · have h1 : (Ltab z : ℝ) = 1 := by exact_mod_cast (Ltab_spec z).1 h
      rw [h1]; ring
    · have h0 : (Ltab z : ℝ) = 0 := by exact_mod_cast (Ltab_spec z).2 h
      rw [h0]; ring
  have hcs : (∑ z : Fin 64, g z * proj g z) ^ 2
      ≤ (∑ z : Fin 64, g z ^ 2) * ∑ z : Fin 64, ((1 - (Ltab z : ℝ)) * proj g z) ^ 2 := by
    simp only [hgr]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hLm : ∑ z : Fin 64, (Ltab z : ℝ) * proj g z ^ 2 = massAll (coef g) := rfl
  have hrr : ∑ z : Fin 64, ((1 - (Ltab z : ℝ)) * proj g z) ^ 2
      = 64 * ∑ a, coef g a ^ 2 - massAll (coef g) := by
    simp only [hr2]
    rw [Finset.sum_sub_distrib, hQQ, hLm]
  have hexp : ∑ z : Fin 64, (g z - proj g z) ^ 2
      = ∑ z : Fin 64, g z ^ 2 - 2 * ∑ z : Fin 64, g z * proj g z
        + ∑ z : Fin 64, proj g z ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    ring
  have hM : (32 - Real.sqrt 848) * ∑ a, coef g a ^ 2 ≤ massAll (coef g) := by
    rw [massAll_massL]; exact coercive (coef g)
  have hG : 0 ≤ ∑ z : Fin 64, g z ^ 2 := Finset.sum_nonneg fun z _ => sq_nonneg (g z)
  have hS : 0 ≤ ∑ a, coef g a ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg (coef g a)
  rw [hgQ, hrr] at hcs
  rw [hexp, hgQ, hQQ]
  rcases hS.lt_or_eq with hSpos | hS0
  · have key : (∑ a, coef g a ^ 2) * (64 ^ 2 * ∑ a, coef g a ^ 2)
        ≤ (∑ a, coef g a ^ 2) * ((∑ z : Fin 64, g z ^ 2) * (32 + Real.sqrt 848)) := by
      nlinarith [mul_nonneg hG (sub_nonneg.mpr hM)]
    nlinarith [key, hSpos]
  · rw [← hS0]
    nlinarith [mul_nonneg hG hs0]

/-- a least-eigenvalue vector of the Gram matrix (the vector of `sharp`) -/
noncomputable def uStar : Fin 18 → ℝ :=
  ![(3 / 212) * Real.sqrt 848, (-5 / 212) * Real.sqrt 848, (-5 / 212) * Real.sqrt 848, (-5 / 212) * Real.sqrt 848, (-5 / 212) * Real.sqrt 848, (-5 / 212) * Real.sqrt 848, (-5 / 212) * Real.sqrt 848, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 4000000 in
theorem uStar_mass : massL uStar = (32 - Real.sqrt 848) * ∑ a, uStar a ^ 2 := by
  have hs : Real.sqrt 848 ^ 2 = 848 := Real.sq_sqrt (by norm_num)
  rw [massL_eq, sumsq_eq]
  simp only [uStar, Matrix.cons_val, Matrix.cons_val_zero]
  linear_combination (3 * Real.sqrt 848 / 848) * hs

set_option maxHeartbeats 4000000 in
/-- `uStar` is an eigenvector: `G uStar = (32 - √848) uStar` -/
theorem uStar_eigen (b : Fin 18) :
    ∑ z : Fin 64, (Ltab z : ℝ) * (∑ a : Fin 18, uStar a * (Xtab z a : ℝ)) * (Xtab z b : ℝ)
      = (32 - Real.sqrt 848) * uStar b := by
  have hs : Real.sqrt 848 ^ 2 = 848 := Real.sq_sqrt (by norm_num)
  fin_cases b
  · simp [Fin.sum_univ_succ, Xtab, Ltab, uStar]
    all_goals linear_combination (3 / 212) * hs
  · simp [Fin.sum_univ_succ, Xtab, Ltab, uStar]
    all_goals linear_combination (-5 / 212) * hs
  · simp [Fin.sum_univ_succ, Xtab, Ltab, uStar]
    all_goals linear_combination (-5 / 212) * hs
  · simp [Fin.sum_univ_succ, Xtab, Ltab, uStar]
    all_goals linear_combination (-5 / 212) * hs
  · simp [Fin.sum_univ_succ, Xtab, Ltab, uStar]
    all_goals linear_combination (-5 / 212) * hs
  · simp [Fin.sum_univ_succ, Xtab, Ltab, uStar]
    all_goals linear_combination (-5 / 212) * hs
  · simp [Fin.sum_univ_succ, Xtab, Ltab, uStar]
    all_goals linear_combination (-5 / 212) * hs
  · simp [Fin.sum_univ_succ, Xtab, Ltab, uStar]
    all_goals ring
  · simp [Fin.sum_univ_succ, Xtab, Ltab, uStar]
    all_goals ring
  · simp [Fin.sum_univ_succ, Xtab, Ltab, uStar]
    all_goals ring
  · simp [Fin.sum_univ_succ, Xtab, Ltab, uStar]
    all_goals ring
  · simp [Fin.sum_univ_succ, Xtab, Ltab, uStar]
    all_goals ring
  · simp [Fin.sum_univ_succ, Xtab, Ltab, uStar]
    all_goals ring
  · simp [Fin.sum_univ_succ, Xtab, Ltab, uStar]
    all_goals ring
  · simp [Fin.sum_univ_succ, Xtab, Ltab, uStar]
    all_goals ring
  · simp [Fin.sum_univ_succ, Xtab, Ltab, uStar]
    all_goals ring
  · simp [Fin.sum_univ_succ, Xtab, Ltab, uStar]
    all_goals ring
  · simp [Fin.sum_univ_succ, Xtab, Ltab, uStar]
    all_goals ring

/-- `𝟙_H q` for the eigenvector `q = ∑_a uStar_a χ_{A_a}` -/
noncomputable def gStar (z : Fin 64) : ℝ :=
  (1 - (Ltab z : ℝ)) * ∑ a : Fin 18, uStar a * (Xtab z a : ℝ)

theorem gStar_coef (b : Fin 18) : coef gStar b = (1 - (32 - Real.sqrt 848) / 64) * uStar b := by
  have h1 : ∑ z : Fin 64, gStar z * (Xtab z b : ℝ)
      = ∑ z : Fin 64, (∑ a : Fin 18, uStar a * (Xtab z a : ℝ)) * (Xtab z b : ℝ)
        - ∑ z : Fin 64, (Ltab z : ℝ) * (∑ a : Fin 18, uStar a * (Xtab z a : ℝ)) * (Xtab z b : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    unfold gStar; ring
  unfold coef
  rw [h1, pair_comb, uStar_eigen]
  ring

theorem gStar_proj (z : Fin 64) :
    proj gStar z = (1 - (32 - Real.sqrt 848) / 64) * ∑ a : Fin 18, uStar a * (Xtab z a : ℝ) := by
  unfold proj
  simp only [gStar_coef]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

set_option maxHeartbeats 4000000 in
/-- **Optimality.** A nonzero function vanishing on `L` attains equality, so `a_*` cannot be
improved -/
theorem coercivity_sharp : ∃ g : Fin 64 → ℝ, (∀ z : Fin 64, changes z.val ≤ 2 → g z = 0) ∧
    g ≠ 0 ∧ ∑ z : Fin 64, (g z - proj g z) ^ 2 = (32 - Real.sqrt 848) / 64 * ∑ z : Fin 64, g z ^ 2 := by
  have hs0 : 0 ≤ Real.sqrt 848 := Real.sqrt_nonneg _
  have hQ : ∑ z : Fin 64, (∑ a : Fin 18, uStar a * (Xtab z a : ℝ)) ^ 2 = 64 * ∑ a, uStar a ^ 2 :=
    total uStar
  have hL : massAll uStar = (32 - Real.sqrt 848) * ∑ a, uStar a ^ 2 := by
    rw [massAll_massL]; exact uStar_mass
  have hg2 : ∀ z, gStar z ^ 2 = (∑ a : Fin 18, uStar a * (Xtab z a : ℝ)) ^ 2
      - (Ltab z : ℝ) * (∑ a : Fin 18, uStar a * (Xtab z a : ℝ)) ^ 2 := by
    intro z
    by_cases h : changes z.val ≤ 2
    · have h1 : (Ltab z : ℝ) = 1 := by exact_mod_cast (Ltab_spec z).1 h
      simp only [gStar]; rw [h1]; ring
    · have h0 : (Ltab z : ℝ) = 0 := by exact_mod_cast (Ltab_spec z).2 h
      simp only [gStar]; rw [h0]; ring
  have hLm : ∑ z : Fin 64, (Ltab z : ℝ) * (∑ a : Fin 18, uStar a * (Xtab z a : ℝ)) ^ 2
      = massAll uStar := rfl
  have hG : ∑ z : Fin 64, gStar z ^ 2 = (64 - (32 - Real.sqrt 848)) * ∑ a, uStar a ^ 2 := by
    simp only [hg2]
    rw [Finset.sum_sub_distrib, hQ, hLm, hL]
    ring
  have h7 : uStar 7 = 1 := by simp [uStar]
  have hS : 0 < ∑ a, uStar a ^ 2 := by
    have := Finset.single_le_sum (fun a _ => sq_nonneg (uStar a)) (Finset.mem_univ (7 : Fin 18))
    rw [h7] at this
    linarith
  refine ⟨gStar, ?_, ?_, ?_⟩
  · intro z h
    have h1 : (Ltab z : ℝ) = 1 := by exact_mod_cast (Ltab_spec z).1 h
    simp only [gStar]; rw [h1]; ring
  · intro h
    have h0 : ∑ z : Fin 64, gStar z ^ 2 = 0 := by simp [h]
    rw [hG] at h0
    have := mul_pos (by linarith : (0 : ℝ) < 64 - (32 - Real.sqrt 848)) hS
    linarith
  · have hd : ∀ z, (gStar z - proj gStar z) ^ 2 = gStar z ^ 2
        - 2 * (1 - (32 - Real.sqrt 848) / 64) * (gStar z * ∑ a : Fin 18, uStar a * (Xtab z a : ℝ))
        + (1 - (32 - Real.sqrt 848) / 64) ^ 2 * (∑ a : Fin 18, uStar a * (Xtab z a : ℝ)) ^ 2 := by
      intro z; rw [gStar_proj]; ring
    have hgq : ∀ z, gStar z * ∑ a : Fin 18, uStar a * (Xtab z a : ℝ) = gStar z ^ 2 := by
      intro z
      by_cases h : changes z.val ≤ 2
      · have h1 : (Ltab z : ℝ) = 1 := by exact_mod_cast (Ltab_spec z).1 h
        simp only [gStar]; rw [h1]; ring
      · have h0 : (Ltab z : ℝ) = 0 := by exact_mod_cast (Ltab_spec z).2 h
        simp only [gStar]; rw [h0]; ring
    simp only [hd, hgq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hG, hQ]
    ring

end SixCycle

#print axioms SixCycle.Lconf_spec
#print axioms SixCycle.Mtab_spec
#print axioms SixCycle.orthonormal
#print axioms SixCycle.coercive
#print axioms SixCycle.sharp
#print axioms SixCycle.rank
#print axioms SixCycle.astar_eq
#print axioms SixCycle.astar_gt

#print axioms SixCycle.Xtab_spec
#print axioms SixCycle.Ltab_spec
#print axioms SixCycle.Xorth
#print axioms SixCycle.proj_orth
#print axioms SixCycle.coercivity
#print axioms SixCycle.coercivity_sharp
