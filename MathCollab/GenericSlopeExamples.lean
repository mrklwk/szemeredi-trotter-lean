module
public import MathCollab.GenericSlope
public import MathCollab.SlopeSubstitutionExamples

@[expose] public section

noncomputable section
open Classical
open MathCollab.GenericSlope

namespace MathCollab.GenericSlopeExamples

example : ringChar (RatFunc (ZMod 2)) = 2 := by
  rw [ringChar_ratFunc]
  exact ringChar.eq (ZMod 2) 2

-- Pure z is retained in the family and becomes a unit after localization.
example : IsUnit (genericFamily (Polynomial.X : Polynomial (MvPolynomial (Fin 2) (ZMod 2)))) := by
  simpa using pure_slope_isUnit (Polynomial.X : Polynomial (ZMod 2)) (by simp)

-- Localization does not turn a nonzero family into zero, but restrictions may be zero.
example : genericFamily (SlopeSubstitutionExamples.exceptionalFamily (K := ZMod 2)) ≠ 0 ∧
    genericRestrict (0, 0)
      (genericFamily (SlopeSubstitutionExamples.exceptionalFamily (K := ZMod 2))) = 0 := by
  constructor
  · exact genericFamily_ne_zero SlopeSubstitutionExamples.exceptionalFamily_ne_zero
  · exact (genericRestrict_eq_zero_iff _ _).mpr
      SlopeSubstitutionExamples.exceptionalFamily_restriction_zero

example : intercept ((0, 0) : ZMod 2 × ZMod 2) ≠ intercept (0, 1) := by
  intro h
  have := intercept_injective h
  norm_num at this

-- The squarefree family over F₂ localizes without any separability or perfection assumption.
example (L : Finset (ZMod 2 × ZMod 2)) (d : ℕ) :
    ∃ S : Polynomial (MvPolynomial (Fin 2) (ZMod 2)),
      genericFamily S ≠ 0 ∧ Squarefree (genericFamily S) ∧ (genericFamily S).totalDegree ≤ d := by
  obtain ⟨S, hS, hsq, _, hd, _⟩ := SquarefreeFamily.exists_squarefree_family L d
  exact ⟨S, genericFamily_ne_zero hS, genericFamily_squarefree hsq hS, genericFamily_totalDegree_le S hd⟩

end MathCollab.GenericSlopeExamples
