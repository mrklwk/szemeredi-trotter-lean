module
public import MathCollab.Exceptional
public import MathCollab.SlopeSubstitutionExamples

@[expose] public section

noncomputable section
open Classical
open MathCollab.Exceptional

namespace MathCollab.ExceptionalExamples
variable {K : Type*} [Field K]

example (S : Polynomial (Plane K)) : exceptionalSet ∅ S = ∅ := by
  simp [exceptionalSet]

-- The nonzero hypothesis is essential: zero restricts to zero at every point.
example (P : Finset (K × K)) : exceptionalSet P 0 = P := by
  simp [exceptionalSet]

-- Pure z is not specialized to zero; as a polynomial it has no exceptional points.
example (P : Finset (K × K)) :
    exceptionalSet P (Polynomial.X : Polynomial (Plane K)) = ∅ := by
  simp [exceptionalSet, SlopeSubstitution.pointRestriction]

example (P : Finset (K × K)) : exceptionalSet P 1 = ∅ := by
  simp [exceptionalSet]

-- Sharp bound |E|=e=1 over F₂, with the actual nonzero family y−zx.
theorem sharp_exceptional_card :
    (exceptionalSet {((0, 0) : ZMod 2 × ZMod 2)}
      SlopeSubstitutionExamples.exceptionalFamily).card = 1 := by
  simp [exceptionalSet, Finset.filter_singleton,
    SlopeSubstitutionExamples.exceptionalFamily_restriction_zero]

example (P : Finset (ZMod 2 × ZMod 2)) :
    (exceptionalSet P SlopeSubstitutionExamples.exceptionalFamily).card ≤ 1 := by
  apply exceptionalSet_card_le P _ SlopeSubstitutionExamples.exceptionalFamily_ne_zero
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le (by simp)
  exact Polynomial.natDegree_mul_le.trans (by simp)

-- No derivative or small-characteristic-degree hypothesis is used in this bound.
example (P : Finset (ZMod 2 × ZMod 2)) (S : Polynomial (Plane (ZMod 2)))
    (hS : S ≠ 0) (he : S.natDegree ≤ 2) : (exceptionalSet P S).card ≤ 2 :=
  exceptionalSet_card_le P S hS he

#print axioms sharp_exceptional_card
end MathCollab.ExceptionalExamples
