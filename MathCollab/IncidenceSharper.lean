module
public import MathCollab.GenericCoordinates

@[expose] public section

/-! A separate strengthening of the checked incidence theorem.
Generic coordinates remove the vertical-line allowance, improving 2m to m.
The original theorem and proof files are unchanged. -/

noncomputable section
open Classical

namespace MathCollab.IncidenceSharper
open IncidenceCounting AffineNormalization IncidenceOptimization
variable {K : Type*} [Field K]

/-- The exact graph-only bound does not pay the extra vertical-line allowance. -/
theorem graph_discrete (P L : Finset (K × K)) (d : ℕ)
    (hc : ringChar K = 0 ∨ d < ringChar K) :
    count P L onGraph ≤ P.card * (slopeHeight L.card d + 1) + d * (d - 1) + L.card := by
  obtain ⟨S, hS, hsq, he, hd, hl⟩ := SquarefreeFamily.exists_squarefree_family L d
  let E := Exceptional.exceptionalSet P S
  have hbudget : (∑ q ∈ P \ E, (degree L onGraph q - slopeHeight L.card d - 1)) ≤
      d * (d - 1) := by
    have h := Parameterized.localized_multiplicity
      (fun q : (P \ E : Finset (K × K)) => (q : K × K)) Subtype.val_injective
      L S hS hsq hc he hd hl
      (fun q => Exceptional.pointRestriction_ne_zero_of_mem_sdiff P S q.property)
    have heq := Finset.sum_coe_sort (P \ E)
      (fun q => degree L onGraph q - slopeHeight L.card d - 1)
    rw [← heq]
    exact h
  exact count_le_of_exceptional_budget P E L onGraph _ _
    (Exceptional.exceptionalSet_subset P S) (graph_pair_unique E L)
    (Exceptional.exceptionalSet_card_le P S hS he) hbudget

/-- The graph-only estimate applies to arbitrary original affine lines by generic coordinates. -/
theorem discrete (P : Finset (K × K)) (L : Finset (Line K)) (d : ℕ)
    (hc : ringChar K = 0 ∨ d < ringChar K) :
    incidenceCount P L ≤ P.card * (slopeHeight L.card d + 1) + d * (d - 1) + L.card := by
  have h := graph_discrete (GenericCoordinates.points P) (GenericCoordinates.lines L) d
    (GenericSlope.characteristic_bound hc)
  simpa only [GenericCoordinates.count_eq, GenericCoordinates.card_points,
    GenericCoordinates.card_lines] using h

theorem augmented_discrete (P : Finset (K × K)) (L : Finset (Line K)) (d : ℕ)
    (hc : ringChar K = 0 ∨ d < ringChar K) :
    incidenceCount P L + P.card ≤ discreteBound P.card L.card d := by
  have h := discrete P L d hc
  have heq : P.card * (slopeHeight L.card d + 1) + P.card =
      P.card * (slopeHeight L.card d + 2) := by ring
  unfold discreteBound
  omega

theorem empty_points (P : Finset (K × K)) (L : Finset (Line K)) (hm : P.card = 0) :
    incidenceCount P L + P.card = 0 := by
  have h := Finset.card_eq_zero.mp hm
  subst P
  simp [incidenceCount, count]

theorem empty_lines (P : Finset (K × K)) (L : Finset (Line K)) (hn : L.card = 0) :
    incidenceCount P L + P.card ≤ P.card := by
  have h := Finset.card_eq_zero.mp hn
  subst L
  simp [incidenceCount, count]

/-- The linear coefficient improves from 2 to 1, with the other constants unchanged. -/
theorem lines_charZero [CharZero K] (P : Finset (K × K)) (L : Finset (Line K)) :
    (incidenceCount P L : ℝ) ≤
      3 * ((P.card : ℝ) * L.card) ^ ((2 : ℝ) / 3) + P.card + L.card := by
  have h := exact_bound_charZero (incidenceCount P L + P.card) P.card L.card L.card le_rfl
    (empty_points P L) (empty_lines P L)
    (fun d _ => augmented_discrete P L d (Or.inl ringChar.eq_zero))
  simp only [Nat.cast_add] at h
  linarith

/-- Positive-characteristic improvement of the linear coefficient, over arbitrary fields. -/
theorem lines_charP (p : ℕ) [CharP K p] (hp : p ≠ 0)
    (P : Finset (K × K)) (L : Finset (Line K)) :
    (incidenceCount P L : ℝ) ≤
      3 * ((P.card : ℝ) * L.card) ^ ((2 : ℝ) / 3) + P.card + L.card +
        2 * P.card * L.card / (p : ℝ) := by
  have hp2 := ((CharP.char_is_prime_or_zero K p).resolve_right hp).two_le
  have h := exact_bound_positiveChar (incidenceCount P L + P.card) P.card L.card L.card p hp2
    le_rfl (empty_points P L) (empty_lines P L)
    (fun d _ hdp => augmented_discrete P L d (Or.inr (by simpa only [ringChar.eq K p] using hdp)))
  simp only [Nat.cast_add] at h
  linarith

/-- Ordinary affine-subspace interface, characteristic zero. -/
theorem affine_charZero [CharZero K] (P : Finset (K × K))
    (L : Finset (AffineSubspace K (K × K)))
    (hL : ∀ l ∈ L, Module.finrank K l.direction = 1) :
    (count P L (fun q l => q ∈ l) : ℝ) ≤
      3 * ((P.card : ℝ) * L.card) ^ ((2 : ℝ) / 3) + P.card + L.card := by
  simpa only [IncidenceTheorem.linesOfAffine_count, IncidenceTheorem.linesOfAffine_card] using
    lines_charZero P (IncidenceTheorem.linesOfAffine L hL)

/-- Ordinary affine-subspace interface, positive characteristic; includes p=2. -/
theorem affine_charP (p : ℕ) [CharP K p] (hp : p ≠ 0) (P : Finset (K × K))
    (L : Finset (AffineSubspace K (K × K)))
    (hL : ∀ l ∈ L, Module.finrank K l.direction = 1) :
    (count P L (fun q l => q ∈ l) : ℝ) ≤
      3 * ((P.card : ℝ) * L.card) ^ ((2 : ℝ) / 3) + P.card + L.card +
        2 * P.card * L.card / (p : ℝ) := by
  simpa only [IncidenceTheorem.linesOfAffine_count, IncidenceTheorem.linesOfAffine_card] using
    lines_charP p hp P (IncidenceTheorem.linesOfAffine L hL)

end MathCollab.IncidenceSharper

#print axioms MathCollab.IncidenceSharper.discrete
#print axioms MathCollab.IncidenceSharper.affine_charZero
#print axioms MathCollab.IncidenceSharper.affine_charP
