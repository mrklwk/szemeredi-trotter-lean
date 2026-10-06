module
public import MathCollab.SlopeSubstitution
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-! Boundary checks for the actual family substitution. In particular, a nonzero
family can have an identically zero point restriction; no nonvanishing is asserted
before the exceptional set is removed. -/

noncomputable section
open Classical
open MathCollab.SlopeSubstitution

namespace MathCollab.SlopeSubstitutionExamples

variable {K : Type*} [Field K]

example (q : K × K) : pointRestriction q 0 = 0 := map_zero _
example (q : K × K) : pointRestriction q 1 = 1 := map_one _

-- Pure slope factors are retained at this stage.
example (q : K × K) : pointRestriction q Polynomial.X = Polynomial.C Polynomial.X := by
  simp [pointRestriction]

-- A nonzero family may vanish identically at an exceptional point.
def exceptionalFamily : Polynomial (MvPolynomial (Fin 2) K) :=
  Polynomial.C (MvPolynomial.X 1) - Polynomial.X * Polynomial.C (MvPolynomial.X 0)

theorem exceptionalFamily_ne_zero : exceptionalFamily (K := K) ≠ 0 := by
  intro h
  have hc := congrArg (fun S : Polynomial (MvPolynomial (Fin 2) K) => S.coeff 0) h
  simp [exceptionalFamily] at hc

theorem exceptionalFamily_restriction_zero :
    pointRestriction (0, 0) (exceptionalFamily (K := K)) = 0 := by
  simp [exceptionalFamily, pointRestriction, planeToUZ]

-- Sharp e+j coefficient degree in characteristic two, even with e=char K.
def sharpFamily : Polynomial (MvPolynomial (Fin 2) (ZMod 2)) :=
  Polynomial.monomial 2 (MvPolynomial.X 1)

theorem sharpFamily_restriction : pointRestriction (0, 0) sharpFamily =
    Polynomial.C (Polynomial.X ^ 3) * Polynomial.X := by
  simp only [sharpFamily, pointRestriction, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_monomial, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  simp [planeToUZ]
  ring

theorem sharpFamily_coefficient : ((pointRestriction (0, 0) sharpFamily).coeff 1).natDegree = 3 := by
  rw [sharpFamily_restriction, Polynomial.coeff_mul_X, Polynomial.coeff_C_zero]
  exact Polynomial.natDegree_X_pow 3

example : sharpFamily.natDegree = 2 := by
  simp [sharpFamily, Polynomial.natDegree_monomial, MvPolynomial.X_ne_zero]

-- Empty line family permits the constant nonzero family with d=e=0.
example : ∃ S : Polynomial (MvPolynomial (Fin 2) (ZMod 2)), S ≠ 0 ∧
    S.natDegree ≤ 0 ∧ (∀ j, (S.coeff j).totalDegree ≤ 0) ∧
    (∀ l ∈ (∅ : Finset (ZMod 2 × ZMod 2)),
      FamilySpace.graphRestrict l.1 l.2 (S.eval (MvPolynomial.C l.1)) = 0) ∧
    ∀ q : ZMod 2 × ZMod 2, (pointRestriction q S).natDegree ≤ 0 ∧
      CoeffBound 0 (pointRestriction q S) ∧
      Polynomial.X ^ (IncidenceCounting.degree ∅ IncidenceCounting.onGraph q - 0) ∣
        pointRestriction q S := by
  simpa [IncidenceOptimization.slopeHeight] using
    exists_family_with_point_restrictions (∅ : Finset (ZMod 2 × ZMod 2)) 0

-- A singleton horizontal line has e=0 and forces a genuinely positive order.
example (t : K) : Polynomial.X ∣
    pointRestriction (t, 0) (Polynomial.C (MvPolynomial.X 1)) := by
  have h := X_pow_incidence_sub_dvd (t, 0) {(0, 0)}
    (Polynomial.C (MvPolynomial.X 1)) (e := 0) (by simp) (by
      intro l hl
      simp only [Finset.mem_singleton] at hl
      subst l
      simp [FamilySpace.graphRestrict])
  simpa [IncidenceCounting.degree, Finset.filter_singleton, IncidenceCounting.onGraph] using h

-- The actual identity bridge includes nonzero slope and a shifted base point.
example (S : Polynomial (MvPolynomial (Fin 2) ℚ)) :
    SlopeForcing.specializeSlope (pointRestriction (2, 7) S) 3 =
      (FamilySpace.graphRestrict 3 1 (S.eval (MvPolynomial.C 3))).comp
        (Polynomial.C 2 + Polynomial.X) :=
  specialize_pointRestriction (2, 7) 3 1 (by norm_num) S

#print axioms exceptionalFamily_ne_zero
#print axioms exceptionalFamily_restriction_zero
#print axioms sharpFamily_coefficient
end MathCollab.SlopeSubstitutionExamples
