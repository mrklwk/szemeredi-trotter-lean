module
public import MathCollab.AffineNormalization

@[expose] public section

/-! Szemerédi–Trotter incidence bounds over arbitrary fields.
Lines are arbitrary one-dimensional affine subspaces of K². Finsets encode finite
sets of distinct points and lines. All constants are explicit, and all algebraic,
normalization, characteristic and empty-case obligations are discharged. -/

noncomputable section
open Classical

namespace MathCollab.IncidenceTheorem

open AffineNormalization
variable {K : Type*} [Field K]

/-- Characteristic-zero form of the paper's full incidence bound. -/
theorem szemeredi_trotter_charZero [CharZero K]
    (P : Finset (K × K)) (L : Finset (Line K)) :
    (incidenceCount P L : ℝ) ≤
      3 * ((P.card : ℝ) * L.card) ^ ((2 : ℝ) / 3) + 2 * P.card + L.card := by
  have h := NormalizedIncidence.exact_charZero P (graphs L) (verticals L)
  rw [← incidenceCount_eq_normalized, card_graphs_add_verticals] at h
  exact h

/-- Positive-characteristic form. p is the field characteristic, not its cardinality.
No assumption of finiteness, perfection or being a prime field is imposed on K. -/
theorem szemeredi_trotter_charP (p : ℕ) [CharP K p] (hp : p ≠ 0)
    (P : Finset (K × K)) (L : Finset (Line K)) :
    (incidenceCount P L : ℝ) ≤
      3 * ((P.card : ℝ) * L.card) ^ ((2 : ℝ) / 3) + 2 * P.card + L.card +
        2 * P.card * L.card / (p : ℝ) := by
  have h := NormalizedIncidence.exact_charP p hp P (graphs L) (verticals L)
  rw [← incidenceCount_eq_normalized, card_graphs_add_verticals] at h
  exact h

/-- Convert a finite set of affine subspaces known to be lines to the bundled line type. -/
def linesOfAffine (L : Finset (AffineSubspace K (K × K)))
    (hL : ∀ l ∈ L, Module.finrank K l.direction = 1) : Finset (Line K) :=
  L.attach.map {
    toFun := fun l : {l : AffineSubspace K (K × K) // l ∈ L} =>
      (⟨l.val, hL l.val l.property⟩ : Line K)
    inj' := by
      intro a b h
      apply Subtype.ext (p := fun l : AffineSubspace K (K × K) => l ∈ L)
      exact congrArg (fun l : Line K => l.val) h
  }

theorem linesOfAffine_card (L : Finset (AffineSubspace K (K × K)))
    (hL : ∀ l ∈ L, Module.finrank K l.direction = 1) : (linesOfAffine L hL).card = L.card := by
  simp [linesOfAffine]

theorem linesOfAffine_count (P : Finset (K × K)) (L : Finset (AffineSubspace K (K × K)))
    (hL : ∀ l ∈ L, Module.finrank K l.direction = 1) :
    incidenceCount P (linesOfAffine L hL) = IncidenceCounting.count P L (fun q l => q ∈ l) := by
  simp only [linesOfAffine, incidenceCount, IncidenceCounting.count, Finset.sum_map]
  exact Finset.sum_attach L (fun l => (P.filter (fun q => q ∈ l)).card)

/-- Unbundled public statement: an arbitrary finite set of affine subspaces of dimension one. -/
theorem affine_charZero [CharZero K] (P : Finset (K × K))
    (L : Finset (AffineSubspace K (K × K)))
    (hL : ∀ l ∈ L, Module.finrank K l.direction = 1) :
    (IncidenceCounting.count P L (fun q l => q ∈ l) : ℝ) ≤
      3 * ((P.card : ℝ) * L.card) ^ ((2 : ℝ) / 3) + 2 * P.card + L.card := by
  simpa only [linesOfAffine_count, linesOfAffine_card] using
    szemeredi_trotter_charZero P (linesOfAffine L hL)

/-- Unbundled public positive-characteristic statement, with all degenerate cases included. -/
theorem affine_charP (p : ℕ) [CharP K p] (hp : p ≠ 0) (P : Finset (K × K))
    (L : Finset (AffineSubspace K (K × K)))
    (hL : ∀ l ∈ L, Module.finrank K l.direction = 1) :
    (IncidenceCounting.count P L (fun q l => q ∈ l) : ℝ) ≤
      3 * ((P.card : ℝ) * L.card) ^ ((2 : ℝ) / 3) + 2 * P.card + L.card +
        2 * P.card * L.card / (p : ℝ) := by
  simpa only [linesOfAffine_count, linesOfAffine_card] using
    szemeredi_trotter_charP p hp P (linesOfAffine L hL)

end MathCollab.IncidenceTheorem

#print axioms MathCollab.IncidenceTheorem.szemeredi_trotter_charZero
#print axioms MathCollab.IncidenceTheorem.szemeredi_trotter_charP
#print axioms MathCollab.IncidenceTheorem.affine_charZero
#print axioms MathCollab.IncidenceTheorem.affine_charP
