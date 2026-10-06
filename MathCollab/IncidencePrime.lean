module
public import MathCollab.FinitePlaneIncidence
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-! The characteristic coefficient improves to one over the prime field F_p.
For mn≤p³ use the checked subcritical bound; otherwise the finite-plane
second-moment bound has error sqrt(pmn)≤(mn)^(2/3). -/

noncomputable section
open Classical

namespace MathCollab.IncidencePrime
open AffineNormalization IncidenceCounting IncidenceOptimization

theorem sqrt_le_two_thirds {a : ℝ} {p : ℕ} (ha : 0 ≤ a) (hcap : (p : ℝ) ^ 3 ≤ a) :
    Real.sqrt ((p : ℝ) * a) ≤ a ^ ((2 : ℝ) / 3) := by
  have hroot : (p : ℝ) ≤ cubeRoot a := by
    by_contra h
    have hpow : cubeRoot a ^ 3 < (p : ℝ) ^ 3 :=
      pow_lt_pow_left₀ (lt_of_not_ge h) (cubeRoot_nonneg ha) (by decide)
    rw [cubeRoot_cube ha] at hpow
    linarith
  have hmul := mul_le_mul_of_nonneg_right hroot ha
  have heq : cubeRoot a * a = (cubeRoot a ^ 2) ^ 2 := by
    calc
      cubeRoot a * a = cubeRoot a * cubeRoot a ^ 3 := by rw [cubeRoot_cube ha]
      _ = _ := by ring
  have h := Real.sqrt_le_sqrt (hmul.trans_eq heq)
  rw [Real.sqrt_sq (sq_nonneg (cubeRoot a)), cubeRoot_sq ha] at h
  exact h

/-- The two regimes combine to give coefficient one on mn/p over F_p. -/
theorem lines (p : ℕ) [Fact (Nat.Prime p)]
    (P : Finset (ZMod p × ZMod p)) (L : Finset (Line (ZMod p))) :
    (incidenceCount P L : ℝ) ≤
      3 * ((P.card : ℝ) * L.card) ^ ((2 : ℝ) / 3) + P.card + L.card +
        P.card * L.card / (p : ℝ) := by
  have hp : Nat.Prime p := Fact.out
  by_cases hcap : P.card * L.card ≤ p ^ 3
  · have h := IncidenceSubcritical.lines p hp.ne_zero P L hcap
    have hterm : (0 : ℝ) ≤ (P.card : ℝ) * L.card / p := by positivity
    linarith
  · have h := FinitePlaneIncidence.lines P L
    simp only [ZMod.card] at h
    have hcap' : (p : ℝ) ^ 3 ≤ (P.card : ℝ) * L.card := by
      exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hcap))
    have hs := sqrt_le_two_thirds (show (0 : ℝ) ≤ (P.card : ℝ) * L.card by positivity) hcap'
    have hn : 0 ≤ ((P.card : ℝ) * L.card) ^ ((2 : ℝ) / 3) := by positivity
    rw [mul_assoc] at h
    linarith [(Nat.cast_nonneg P.card : (0 : ℝ) ≤ P.card),
      (Nat.cast_nonneg L.card : (0 : ℝ) ≤ L.card)]

/-- The prime-field theorem for ordinary affine subspaces of dimension one.
The field is exactly ZMod p with prime p; this is not asserted for every field
of characteristic p or for arbitrary finite extensions. -/
theorem affine (p : ℕ) [Fact (Nat.Prime p)] (P : Finset (ZMod p × ZMod p))
    (L : Finset (AffineSubspace (ZMod p) (ZMod p × ZMod p)))
    (hL : ∀ l ∈ L, Module.finrank (ZMod p) l.direction = 1) :
    (count P L (fun q l => q ∈ l) : ℝ) ≤
      3 * ((P.card : ℝ) * L.card) ^ ((2 : ℝ) / 3) + P.card + L.card +
        P.card * L.card / (p : ℝ) := by
  simpa only [IncidenceTheorem.linesOfAffine_count, IncidenceTheorem.linesOfAffine_card] using
    lines p P (IncidenceTheorem.linesOfAffine L hL)

end MathCollab.IncidencePrime

#print axioms MathCollab.IncidencePrime.affine
