module
public import MathCollab.IncidenceOptimization

@[expose] public section

/-! Boundary checks for integer rounding, clipping, empty cases, and exact constants. -/

noncomputable section
open MathCollab.IncidenceOptimization

-- Natural division rounds down, including at a nonintegral quotient.
example : slopeHeight 1 1 = 0 := by decide
example : slopeHeight 3 1 = 2 := by decide
example : 2 * 1 < (slopeHeight 1 1 + 1) * (1 + 2) := slopeHeight_strict 1 1

private theorem cubeRoot_eight : cubeRoot 8 = 2 := by
  have h := Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 2) (by decide : (3 : ℕ) ≠ 0)
  norm_num [cubeRoot] at h ⊢

example : floorDegree 1 = 1 := by norm_num [floorDegree, cubeRoot]
example : floorDegree 8 = 2 := by norm_num [floorDegree, cubeRoot_eight]

-- A noncube input lies strictly between successive cubes, so its floor is one.
example : floorDegree 2 = 1 := by
  have hlo := one_le_cubeRoot (by norm_num : (1 : ℝ) ≤ 2)
  have hhi : cubeRoot 2 < cubeRoot 8 :=
    Real.rpow_lt_rpow (by norm_num) (by norm_num) (by norm_num)
  rw [cubeRoot_eight] at hhi
  apply (Nat.floor_eq_iff (by linarith : 0 ≤ cubeRoot 2)).mpr
  norm_num
  exact And.intro hlo hhi

-- Actually clipped, exactly on the cutoff, and below the cutoff.
example : clippedDegree 8 2 = 1 := by norm_num [clippedDegree, floorDegree, cubeRoot_eight]
example : clippedDegree 8 3 = 2 := by norm_num [clippedDegree, floorDegree, cubeRoot_eight]
example : clippedDegree 8 5 = 2 := by norm_num [clippedDegree, floorDegree, cubeRoot_eight]

-- Empty points and arbitrary total line count, in characteristic zero.
example (n : ℕ) :
    (0 : ℝ) ≤ 3 * ((0 : ℝ) * n) ^ ((2 : ℝ) / 3) + 2 * 0 + n := by
  simpa only [Nat.cast_zero] using exact_bound_charZero 0 0 0 n (by omega) (by simp) (by simp)
    (by intro d _; exact Nat.zero_le _)

-- Only vertical incidences, including p=2 and arbitrary m, n.
example (m n : ℕ) :
    (m : ℝ) ≤ 3 * ((m : ℝ) * n) ^ ((2 : ℝ) / 3) + 2 * m + n + 2 * m * n / 2 := by
  apply exact_bound_positiveChar m m 0 n 2 (by omega) (by omega)
  · exact fun h => h
  · intro _; rfl
  · intro d _ _
    simp only [discreteBound, slopeHeight, Nat.mul_zero, Nat.zero_div, Nat.zero_add, Nat.add_zero]
    omega

-- A graph line and a vertical line through one point: n₀<n tests monotonicity.
example : (2 : ℝ) ≤ 3 * ((1 : ℝ) * 2) ^ ((2 : ℝ) / 3) + 2 * 1 + 2 := by
  have hparameter : ∀ d : ℕ, 1 ≤ d → 2 ≤ discreteBound 1 1 d := by
    intro d _
    simp only [discreteBound, Nat.one_mul]
    omega
  simpa using exact_bound_charZero 2 1 1 2 (by decide) (by omega) (by omega) hparameter

-- The full affine plane over F₂: I=12, m=4, n₀=4, n=6, characteristic p=2.
-- Only d=1 is admissible; the exact natural parameter is e=floor(8/3)=2.
example : (12 : ℝ) ≤ 3 * ((4 : ℝ) * 6) ^ ((2 : ℝ) / 3) + 2 * 4 + 6 + 2 * 4 * 6 / 2 := by
  apply exact_bound_positiveChar 12 4 4 6 2 (by decide) (by decide) (by omega) (by omega)
  intro d hd hdp
  have : d = 1 := by omega
  subst d
  norm_num [discreteBound, slopeHeight]
