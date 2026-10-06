module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic

@[expose] public section

/-! Exact numerical optimization for Section 4 of arXiv:2609.27023v2.
Incidence estimates are explicit hypotheses; this module proves no polynomial
or geometric estimate. All real exponents and natural divisions are explicit. -/

noncomputable section

namespace MathCollab.IncidenceOptimization

/-- The exact natural floor parameter used in the polynomial family. -/
def slopeHeight (n d : ℕ) : ℕ := (2 * n) / (d + 2)

/-- The exact discrete bound, including vertical incidences. -/
def discreteBound (m n d : ℕ) : ℕ := m * (slopeHeight n d + 2) + d * (d - 1) + n

def cubeRoot (a : ℝ) : ℝ := a ^ ((1 : ℝ) / 3)
def floorDegree (a : ℝ) : ℕ := ⌊cubeRoot a⌋₊
def clippedDegree (a : ℝ) (p : ℕ) : ℕ := min (floorDegree a) (p - 1)

theorem cubeRoot_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ cubeRoot a :=
  Real.rpow_nonneg ha _

theorem cubeRoot_cube {a : ℝ} (ha : 0 ≤ a) : cubeRoot a ^ 3 = a := by
  have h := Real.rpow_mul_natCast ha ((1 : ℝ) / 3) 3
  norm_num [cubeRoot] at h ⊢
  exact h.symm

theorem cubeRoot_sq {a : ℝ} (ha : 0 ≤ a) : cubeRoot a ^ 2 = a ^ ((2 : ℝ) / 3) := by
  have h := Real.rpow_mul_natCast ha ((1 : ℝ) / 3) 2
  norm_num [cubeRoot] at h ⊢
  exact h.symm

theorem one_le_cubeRoot {a : ℝ} (ha : 1 ≤ a) : 1 ≤ cubeRoot a :=
  Real.one_le_rpow ha (by norm_num)

theorem floorDegree_properties {a : ℝ} (ha : 1 ≤ a) :
    1 ≤ floorDegree a ∧ (floorDegree a : ℝ) ≤ cubeRoot a ∧
      cubeRoot a < (floorDegree a : ℝ) + 2 := by
  have hroot := one_le_cubeRoot ha
  refine ⟨(Nat.one_le_floor_iff _).mpr hroot, Nat.floor_le (by linarith), ?_⟩
  have h := Nat.lt_floor_add_one (cubeRoot a)
  change cubeRoot a < (Nat.floor (cubeRoot a) : ℝ) + 2
  linarith

/-- The clipped choice is legal even when p=2; one denominator comparison holds. -/
theorem clippedDegree_properties {a : ℝ} {p : ℕ} (ha : 1 ≤ a) (hp : 2 ≤ p) :
    1 ≤ clippedDegree a p ∧ clippedDegree a p < p ∧
      (clippedDegree a p : ℝ) ≤ cubeRoot a ∧
      (cubeRoot a < (clippedDegree a p : ℝ) + 2 ∨
        (p : ℝ) < (clippedDegree a p : ℝ) + 2) := by
  obtain ⟨hf, hfle, hflt⟩ := floorDegree_properties ha
  have hge : 1 ≤ clippedDegree a p := by
    exact le_min hf (by omega)
  have hlt : clippedDegree a p < p := by
    have h := min_le_right (floorDegree a) (p - 1)
    change min (floorDegree a) (p - 1) < p
    omega
  have hle : (clippedDegree a p : ℝ) ≤ cubeRoot a := by
    apply le_trans _ hfle
    exact_mod_cast min_le_left (floorDegree a) (p - 1)
  refine ⟨hge, hlt, hle, ?_⟩
  by_cases h : floorDegree a ≤ p - 1
  · exact Or.inl (by simpa [clippedDegree, min_eq_left h] using hflt)
  · right
    have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    simp only [clippedDegree, min_eq_right (by omega : p - 1 ≤ floorDegree a), hcast]
    linarith

/-- Natural division gives the required real upper bound without rounding loss. -/
theorem slopeHeight_le (n d : ℕ) :
    (slopeHeight n d : ℝ) ≤ 2 * (n : ℝ) / ((d : ℝ) + 2) := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (d : ℝ) + 2)).mpr
  have h := Nat.div_mul_le_self (2 * n) (d + 2)
  exact_mod_cast h

/-- The same natural floor gives the strict coefficient-count inequality. -/
theorem slopeHeight_strict (n d : ℕ) :
    2 * n < (slopeHeight n d + 1) * (d + 2) := by
  have hlt := Nat.mod_lt (2 * n) (by omega : 0 < d + 2)
  have heq := Nat.mod_add_div (2 * n) (d + 2)
  dsimp [slopeHeight]
  nlinarith

theorem discreteBound_le_relaxed (m n d : ℕ) :
    (discreteBound m n d : ℝ) ≤
      2 * (m : ℝ) + n + 2 * m * n / ((d : ℝ) + 2) + (d : ℝ) ^ 2 := by
  have he := slopeHeight_le n d
  have hm := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  have hd : (d : ℝ) * ((d - 1 : ℕ) : ℝ) ≤ (d : ℝ) * d := by
    exact_mod_cast Nat.mul_le_mul_left d (Nat.sub_le d 1)
  simp only [discreteBound, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  calc
    (m : ℝ) * ((slopeHeight n d : ℝ) + 2) + d * ((d - 1 : ℕ) : ℝ) + n ≤
        m * (2 * n / ((d : ℝ) + 2) + 2) + (d : ℝ) ^ 2 + n := by nlinarith
    _ = _ := by ring

theorem quotient_le_root_sq {a : ℝ} {d : ℕ} (ha : 1 ≤ a)
    (hden : cubeRoot a < (d : ℝ) + 2) :
    2 * a / ((d : ℝ) + 2) ≤ 2 * cubeRoot a ^ 2 := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (d : ℝ) + 2)).mpr
  have hc := cubeRoot_cube (show 0 ≤ a by linarith)
  have hm := mul_le_mul_of_nonneg_left hden.le (show 0 ≤ 2 * cubeRoot a ^ 2 by positivity)
  nlinarith

theorem floorDegree_relaxed_le {a : ℝ} (ha : 1 ≤ a) :
    2 * a / ((floorDegree a : ℝ) + 2) + (floorDegree a : ℝ) ^ 2 ≤
      3 * a ^ ((2 : ℝ) / 3) := by
  obtain ⟨_, hle, hden⟩ := floorDegree_properties ha
  have hq := quotient_le_root_sq ha hden
  have hs : (floorDegree a : ℝ) ^ 2 ≤ cubeRoot a ^ 2 := by
    nlinarith [cubeRoot_nonneg (show 0 ≤ a by linarith),
      (Nat.cast_nonneg (floorDegree a) : (0 : ℝ) ≤ floorDegree a)]
  rw [← cubeRoot_sq (show 0 ≤ a by linarith)]
  linarith

theorem clippedDegree_relaxed_le {a : ℝ} {p : ℕ} (ha : 1 ≤ a) (hp : 2 ≤ p) :
    2 * a / ((clippedDegree a p : ℝ) + 2) + (clippedDegree a p : ℝ) ^ 2 ≤
      3 * a ^ ((2 : ℝ) / 3) + 2 * a / (p : ℝ) := by
  obtain ⟨_, _, hle, hden⟩ := clippedDegree_properties ha hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hs : (clippedDegree a p : ℝ) ^ 2 ≤ cubeRoot a ^ 2 := by
    nlinarith [cubeRoot_nonneg (show 0 ≤ a by linarith),
      (Nat.cast_nonneg (clippedDegree a p) : (0 : ℝ) ≤ clippedDegree a p)]
  rw [← cubeRoot_sq (show 0 ≤ a by linarith)]
  rcases hden with hden | hden
  · have hq := quotient_le_root_sq ha hden
    have hn : 0 ≤ 2 * a / (p : ℝ) := by positivity
    linarith
  · have hq : 2 * a / ((clippedDegree a p : ℝ) + 2) ≤ 2 * a / (p : ℝ) :=
      div_le_div_of_nonneg_left (by linarith) hp0 hden.le
    nlinarith [sq_nonneg (cubeRoot a)]

/-- Exact characteristic-zero numerical conclusion, conditional on the supplied
discrete estimate and elementary empty/vertical cases. Here n₀ counts graph lines. -/
theorem exact_bound_charZero (I m n₀ n : ℕ) (hn : n₀ ≤ n)
    (h_empty : m = 0 → I = 0) (h_vertical : n₀ = 0 → I ≤ m)
    (h_parameter : ∀ d : ℕ, 1 ≤ d → I ≤ discreteBound m n₀ d) :
    (I : ℝ) ≤ 3 * ((m : ℝ) * n) ^ ((2 : ℝ) / 3) + 2 * m + n := by
  by_cases hm : m = 0
  · have hi := h_empty hm
    subst m
    subst I
    simp only [Nat.cast_zero]
    positivity
  by_cases hn₀ : n₀ = 0
  · have hi : (I : ℝ) ≤ m := by exact_mod_cast h_vertical hn₀
    have hr := Real.rpow_nonneg (show (0 : ℝ) ≤ (m : ℝ) * n by positivity) ((2 : ℝ) / 3)
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have ha : 1 ≤ (m : ℝ) * n₀ := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.mul_pos (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn₀)))
  have hd := (floorDegree_properties ha).1
  have hi : (I : ℝ) ≤ discreteBound m n₀ (floorDegree ((m : ℝ) * n₀)) := by
    exact_mod_cast h_parameter _ hd
  have hrelax := discreteBound_le_relaxed m n₀ (floorDegree ((m : ℝ) * n₀))
  have hopt := floorDegree_relaxed_le ha
  have hnR : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hprod : (m : ℝ) * n₀ ≤ (m : ℝ) * n :=
    mul_le_mul_of_nonneg_left hnR (Nat.cast_nonneg m)
  have hpow := Real.rpow_le_rpow (show (0 : ℝ) ≤ (m : ℝ) * n₀ by positivity)
    hprod (by norm_num : (0 : ℝ) ≤ 2 / 3)
  simp only [mul_assoc] at hrelax
  linarith only [hi, hrelax, hopt, hpow, hnR]

/-- Exact positive-characteristic numerical conclusion. The number p is the
characteristic cutoff (not field cardinality); the supplied estimate is required
only for 1≤d<p. Arithmetic needs p≥2, including the boundary p=2. -/
theorem exact_bound_positiveChar (I m n₀ n p : ℕ) (hp : 2 ≤ p) (hn : n₀ ≤ n)
    (h_empty : m = 0 → I = 0) (h_vertical : n₀ = 0 → I ≤ m)
    (h_parameter : ∀ d : ℕ, 1 ≤ d → d < p → I ≤ discreteBound m n₀ d) :
    (I : ℝ) ≤ 3 * ((m : ℝ) * n) ^ ((2 : ℝ) / 3) + 2 * m + n +
      2 * m * n / (p : ℝ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  by_cases hm : m = 0
  · have hi := h_empty hm
    subst m
    subst I
    simp only [Nat.cast_zero]
    positivity
  by_cases hn₀ : n₀ = 0
  · have hi : (I : ℝ) ≤ m := by exact_mod_cast h_vertical hn₀
    have hr := Real.rpow_nonneg (show (0 : ℝ) ≤ (m : ℝ) * n by positivity) ((2 : ℝ) / 3)
    have ht : (0 : ℝ) ≤ 2 * m * n / (p : ℝ) := by positivity
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have ha : 1 ≤ (m : ℝ) * n₀ := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.mul_pos (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn₀)))
  obtain ⟨hd, hdp, _, _⟩ := clippedDegree_properties ha hp
  have hi : (I : ℝ) ≤ discreteBound m n₀ (clippedDegree ((m : ℝ) * n₀) p) := by
    exact_mod_cast h_parameter _ hd hdp
  have hrelax := discreteBound_le_relaxed m n₀ (clippedDegree ((m : ℝ) * n₀) p)
  have hopt := clippedDegree_relaxed_le ha hp
  have hnR : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hprod : (m : ℝ) * n₀ ≤ (m : ℝ) * n :=
    mul_le_mul_of_nonneg_left hnR (Nat.cast_nonneg m)
  have hpow := Real.rpow_le_rpow (show (0 : ℝ) ≤ (m : ℝ) * n₀ by positivity)
    hprod (by norm_num : (0 : ℝ) ≤ 2 / 3)
  have hdiv : 2 * ((m : ℝ) * n₀) / (p : ℝ) ≤ 2 * ((m : ℝ) * n) / (p : ℝ) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by norm_num)) hp0.le
  simp only [mul_assoc] at hrelax ⊢
  linarith only [hi, hrelax, hopt, hpow, hdiv, hnR]

end MathCollab.IncidenceOptimization

#print axioms MathCollab.IncidenceOptimization.slopeHeight_strict
#print axioms MathCollab.IncidenceOptimization.floorDegree_properties
#print axioms MathCollab.IncidenceOptimization.clippedDegree_properties
#print axioms MathCollab.IncidenceOptimization.exact_bound_charZero
#print axioms MathCollab.IncidenceOptimization.exact_bound_positiveChar
