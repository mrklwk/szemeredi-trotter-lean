module
public import MathCollab.IncidenceSharper

@[expose] public section

/-! Below mn≤p³, the characteristic term is unnecessary, with the same leading
constant and the improved linear terms. This is a case split, not a uniform
claim that the characteristic coefficient can be halved. -/

noncomputable section
open Classical

namespace MathCollab.IncidenceSubcritical
open IncidenceOptimization IncidenceCounting AffineNormalization

theorem clipped_relaxed_le {a : ℝ} {p : ℕ} (ha : 1 ≤ a) (hp : 2 ≤ p)
    (hcap : a ≤ (p : ℝ) ^ 3) :
    2 * a / ((clippedDegree a p : ℝ) + 2) + (clippedDegree a p : ℝ) ^ 2 ≤
      3 * a ^ ((2 : ℝ) / 3) := by
  have ha0 : 0 ≤ a := by linarith
  have hroot : cubeRoot a ≤ (p : ℝ) := by
    by_contra h
    have hpow : (p : ℝ) ^ 3 < cubeRoot a ^ 3 :=
      pow_lt_pow_left₀ (lt_of_not_ge h) (by positivity) (by decide)
    rw [cubeRoot_cube ha0] at hpow
    linarith
  obtain ⟨_, _, hle, hden⟩ := clippedDegree_properties ha hp
  have hden' : cubeRoot a < (clippedDegree a p : ℝ) + 2 :=
    hden.elim id (lt_of_le_of_lt hroot)
  have hq := quotient_le_root_sq ha hden'
  have hs : (clippedDegree a p : ℝ) ^ 2 ≤ cubeRoot a ^ 2 := by
    nlinarith [cubeRoot_nonneg ha0,
      (Nat.cast_nonneg (clippedDegree a p) : (0 : ℝ) ≤ clippedDegree a p)]
  rw [← cubeRoot_sq ha0]
  linarith

variable {K : Type*} [Field K]

/-- No characteristic term is needed when the point-line product is at most p³. -/
theorem lines (p : ℕ) [CharP K p] (hp : p ≠ 0)
    (P : Finset (K × K)) (L : Finset (Line K)) (hcap : P.card * L.card ≤ p ^ 3) :
    (incidenceCount P L : ℝ) ≤
      3 * ((P.card : ℝ) * L.card) ^ ((2 : ℝ) / 3) + P.card + L.card := by
  by_cases hm : P.card = 0
  · have hz : incidenceCount P L = 0 := by
      have h := IncidenceSharper.empty_points P L hm
      omega
    simp only [hz, Nat.cast_zero]
    positivity
  by_cases hn : L.card = 0
  · have hz : incidenceCount P L = 0 := by
      have h := IncidenceSharper.empty_lines P L hn
      omega
    simp only [hz, Nat.cast_zero]
    positivity
  have ha : 1 ≤ (P.card : ℝ) * L.card := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.mul_pos (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn))
  have hp2 := ((CharP.char_is_prime_or_zero K p).resolve_right hp).two_le
  obtain ⟨hd, hdp, _, _⟩ := clippedDegree_properties ha hp2
  have hi : (incidenceCount P L : ℝ) + P.card ≤
      discreteBound P.card L.card (clippedDegree ((P.card : ℝ) * L.card) p) := by
    exact_mod_cast IncidenceSharper.augmented_discrete P L
      (clippedDegree ((P.card : ℝ) * L.card) p)
      (Or.inr (by simpa only [ringChar.eq K p] using hdp))
  have hr := discreteBound_le_relaxed P.card L.card (clippedDegree ((P.card : ℝ) * L.card) p)
  have hopt := clipped_relaxed_le ha hp2 (show (P.card : ℝ) * L.card ≤ (p : ℝ) ^ 3 by exact_mod_cast hcap)
  simp only [mul_assoc] at hr
  linarith

theorem affine (p : ℕ) [CharP K p] (hp : p ≠ 0) (P : Finset (K × K))
    (L : Finset (AffineSubspace K (K × K)))
    (hL : ∀ l ∈ L, Module.finrank K l.direction = 1) (hcap : P.card * L.card ≤ p ^ 3) :
    (count P L (fun q l => q ∈ l) : ℝ) ≤
      3 * ((P.card : ℝ) * L.card) ^ ((2 : ℝ) / 3) + P.card + L.card := by
  simpa only [IncidenceTheorem.linesOfAffine_count, IncidenceTheorem.linesOfAffine_card] using
    lines p hp P (IncidenceTheorem.linesOfAffine L hL)
      (by simpa only [IncidenceTheorem.linesOfAffine_card] using hcap)

end MathCollab.IncidenceSubcritical

#print axioms MathCollab.IncidenceSubcritical.affine
