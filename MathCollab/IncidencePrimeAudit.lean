module
public import MathCollab.IncidencePrime

@[expose] public section

noncomputable section
open Classical
open scoped BigOperators

namespace MathCollab.IncidencePrimeAudit

/-- The public count agrees with the cardinality of incident point-line pairs. -/
theorem count_eq_pairs {A B : Type*} (P : Finset A) (L : Finset B) (R : A → B → Prop) :
    IncidenceCounting.count P L R = ((P ×ˢ L).filter (fun z => R z.1 z.2)).card := by
  simp only [IncidenceCounting.count, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.sum_product]
  exact Finset.sum_comm

/-- The prime-field result stated without the project's incidence-count wrapper. -/
theorem paper_prime (p : ℕ) [Fact (Nat.Prime p)]
    (P : Finset (ZMod p × ZMod p))
    (L : Finset (AffineSubspace (ZMod p) (ZMod p × ZMod p)))
    (hL : ∀ l ∈ L, Module.finrank (ZMod p) l.direction = 1) :
    (((P ×ˢ L).filter (fun z => z.1 ∈ z.2)).card : ℝ) ≤
      3 * ((P.card : ℝ) * (L.card : ℝ)) ^ ((2 : ℝ) / 3) +
        (P.card : ℝ) + (L.card : ℝ) + (P.card : ℝ) * (L.card : ℝ) / (p : ℝ) := by
  rw [← count_eq_pairs P L (fun q l => q ∈ l)]
  exact IncidencePrime.affine p P L hL

-- The field of two elements is included; no large-prime assumption occurs.
example (P : Finset (ZMod 2 × ZMod 2))
    (L : Finset (AffineSubspace (ZMod 2) (ZMod 2 × ZMod 2)))
    (hL : ∀ l ∈ L, Module.finrank (ZMod 2) l.direction = 1) :
    (((P ×ˢ L).filter (fun z => z.1 ∈ z.2)).card : ℝ) ≤
      3 * ((P.card : ℝ) * (L.card : ℝ)) ^ ((2 : ℝ) / 3) +
        (P.card : ℝ) + (L.card : ℝ) + (P.card : ℝ) * (L.card : ℝ) / (2 : ℝ) :=
  paper_prime 2 P L hL

-- The square-root comparison also holds at the exact regime boundary.
example (p : ℕ) :
    Real.sqrt ((p : ℝ) * (p : ℝ) ^ 3) ≤ ((p : ℝ) ^ 3) ^ ((2 : ℝ) / 3) :=
  IncidencePrime.sqrt_le_two_thirds (by positivity) le_rfl

-- The full plane over F_2 has four points, six lines and twelve incidences.
-- The product 24 exceeds p^3=8, so this checks the large-product geometry.
example : IncidenceCounting.count (Finset.univ : Finset (ZMod 2 × ZMod 2))
    (Finset.univ : Finset (AffineNormalization.NormalForm (ZMod 2)))
    AffineNormalization.onNormalForm = 12 := by
  simp [IncidenceCounting.count, FinitePlaneIncidence.line_card, ZMod.card,
    Fintype.card_sum, Fintype.card_prod]

-- The variance argument counts vertical as well as graph lines.
example : ((Finset.univ : Finset (ZMod 2 × ZMod 2)).filter
    (fun q => AffineNormalization.onNormalForm q (Sum.inr 1))).card = 2 := by
  simpa only [ZMod.card] using FinitePlaneIncidence.line_card (Sum.inr (1 : ZMod 2))

end MathCollab.IncidencePrimeAudit

#check @MathCollab.IncidencePrime.affine
#print axioms MathCollab.FinitePlaneIncidence.variance_le
#print axioms MathCollab.FinitePlaneIncidence.lines
#print axioms MathCollab.IncidencePrime.affine
#print axioms MathCollab.IncidencePrimeAudit.paper_prime
