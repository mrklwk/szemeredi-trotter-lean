module
public import MathCollab.SquarefreeFamily
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Nilpotent.Lemmas

@[expose] public section

/-! The specific localization K[z] → K(z), with no specialization to a field element.
Squarefreeness is transported using radical principal ideals under localization,
not an arbitrary extension-of-fields assertion. -/

noncomputable section
open Classical

namespace MathCollab.GenericSlope

variable {K : Type*} [Field K]

/-- Extend only the z-coefficient ring to its rational-function field. -/
def coefficientMap : MvPolynomial (Fin 2) (Polynomial K) →+* MvPolynomial (Fin 2) (RatFunc K) :=
  MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K))

/-- Regard the actual family as a plane polynomial over K(z). -/
def genericFamily : Polynomial (MvPolynomial (Fin 2) K) →+* MvPolynomial (Fin 2) (RatFunc K) :=
  coefficientMap.comp SquarefreeFamily.reorder.toRingHom

theorem coefficientMap_injective : Function.Injective (coefficientMap (K := K)) :=
  MvPolynomial.map_injective _ (RatFunc.algebraMap_injective K)

theorem genericFamily_injective : Function.Injective (genericFamily (K := K)) :=
  coefficientMap_injective.comp SquarefreeFamily.reorder.injective

theorem genericFamily_ne_zero {S : Polynomial (MvPolynomial (Fin 2) K)} (hS : S ≠ 0) :
    genericFamily S ≠ 0 :=
  fun h => hS (genericFamily_injective (h.trans (map_zero genericFamily).symm))

/-- Squarefreeness survives a localization when the image remains nonzero. -/
theorem squarefree_algebraMap_of_isLocalization {A B : Type*}
    [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
    [CommRing B] [IsDomain B] (M : Submonoid A) [Algebra A B] [IsLocalization M B]
    {x : A} (hsq : Squarefree x) (hne : algebraMap A B x ≠ 0) :
    Squarefree (algebraMap A B x) := by
  apply IsRadical.squarefree hne
  rw [isRadical_iff_span_singleton]
  have hr := IsLocalization.map_radical M B (Ideal.span ({x} : Set A))
  rw [(isRadical_iff_span_singleton.mp hsq.isRadical).radical] at hr
  apply Ideal.radical_eq_iff.mp
  simpa only [Ideal.map_span, Set.image_singleton] using hr.symm

theorem squarefree_reorder {S : Polynomial (MvPolynomial (Fin 2) K)} (hsq : Squarefree S) :
    Squarefree (SquarefreeFamily.reorder S) := by
  intro D hD
  have h : SquarefreeFamily.reorder.symm D * SquarefreeFamily.reorder.symm D ∣ S := by
    simpa using map_dvd SquarefreeFamily.reorder.symm hD
  simpa using (hsq _ h).map SquarefreeFamily.reorder

/-- This coefficient map is a localization at the nonzero polynomials in z. -/
theorem coefficientMap_squarefree {F : MvPolynomial (Fin 2) (Polynomial K)}
    (hsq : Squarefree F) (hne : F ≠ 0) : Squarefree (coefficientMap F) := by
  let := MvPolynomial.algebraMvPolynomial (σ := Fin 2) (R := Polynomial K) (S := RatFunc K)
  apply squarefree_algebraMap_of_isLocalization
    ((nonZeroDivisors (Polynomial K)).map (MvPolynomial.C (σ := Fin 2))) hsq
  change coefficientMap F ≠ 0
  exact fun h => hne (coefficientMap_injective (h.trans (map_zero coefficientMap).symm))

theorem genericFamily_squarefree {S : Polynomial (MvPolynomial (Fin 2) K)}
    (hsq : Squarefree S) (hne : S ≠ 0) : Squarefree (genericFamily S) := by
  apply coefficientMap_squarefree (squarefree_reorder hsq)
  exact fun h => hne (SquarefreeFamily.reorder.injective
    (h.trans (map_zero SquarefreeFamily.reorder).symm))

/-- The plane bound remains d after localization; no degree in z is added. -/
theorem genericFamily_totalDegree_le (S : Polynomial (MvPolynomial (Fin 2) K))
    {d : ℕ} (hd : ∀ j, (S.coeff j).totalDegree ≤ d) :
    (genericFamily S).totalDegree ≤ d := by
  change (MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K))
    (SquarefreeFamily.reorder S)).totalDegree ≤ d
  rw [MvPolynomial.totalDegree,
    MvPolynomial.support_map_of_injective _ (RatFunc.algebraMap_injective K)]
  exact (SquarefreeFamily.totalDegree_reorder_le_iff S d).mpr hd

/-- K and K(z) have the same characteristic, including characteristic two. -/
theorem ringChar_ratFunc : ringChar (RatFunc K) = ringChar K :=
  (Algebra.ringChar_eq K (RatFunc K)).symm

theorem characteristic_bound {d : ℕ} (hc : ringChar K = 0 ∨ d < ringChar K) :
    ringChar (RatFunc K) = 0 ∨ d < ringChar (RatFunc K) := by
  simpa only [ringChar_ratFunc] using hc

/-- Intercept of the auxiliary line y=z*x+(q₂−z*q₁) over K(z). -/
def intercept (q : K × K) : RatFunc K := RatFunc.C q.2 - RatFunc.X * RatFunc.C q.1

theorem point_on_auxiliary_line (q : K × K) :
    RatFunc.C q.2 = RatFunc.X * RatFunc.C q.1 + intercept q := by
  simp [intercept]

/-- Distinct original points produce distinct parallel lines over K(z). -/
theorem intercept_injective : Function.Injective (intercept (K := K)) := by
  intro q r h
  have hp : Polynomial.C q.2 - Polynomial.X * Polynomial.C q.1 =
      Polynomial.C r.2 - Polynomial.X * Polynomial.C r.1 := by
    apply RatFunc.algebraMap_injective K
    simpa only [intercept, map_sub, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X] using h
  have h0 := congrArg (fun P : Polynomial K => P.coeff 0) hp
  have h1 := congrArg (fun P : Polynomial K => P.coeff 1) hp
  apply Prod.ext
  · simpa using h1
  · simpa using h0

/-- Restrict a plane polynomial over K(z) to q+u(1,z). -/
def genericRestrict (q : K × K) :
    MvPolynomial (Fin 2) (RatFunc K) →ₐ[RatFunc K] Polynomial (RatFunc K) :=
  MvPolynomial.aeval ![Polynomial.C (RatFunc.C q.1) + Polynomial.X,
    Polynomial.C (RatFunc.C q.2) + Polynomial.C RatFunc.X * Polynomial.X]

@[simp] theorem genericFamily_C (F : MvPolynomial (Fin 2) K) :
    genericFamily (Polynomial.C F) = MvPolynomial.map RatFunc.C F := by
  simp [genericFamily, coefficientMap, MvPolynomial.map_map]

@[simp] theorem genericFamily_X :
    genericFamily (Polynomial.X : Polynomial (MvPolynomial (Fin 2) K)) =
      MvPolynomial.C RatFunc.X := by
  simp [genericFamily, coefficientMap]

theorem restrict_planeToUZ (q : K × K) (F : MvPolynomial (Fin 2) K) :
    genericRestrict q (MvPolynomial.map RatFunc.C F) =
      (Polynomial.mapRingHom (algebraMap (Polynomial K) (RatFunc K)))
        (SlopeSubstitution.planeToUZ q F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [genericRestrict, SlopeSubstitution.planeToUZ, Polynomial.algebraMap_eq]
  | add F G hF hG => simp only [map_add, hF, hG]
  | mul_X F i hF =>
    simp only [map_mul, hF]
    congr 1
    fin_cases i <;> simp [genericRestrict, SlopeSubstitution.planeToUZ]

/-- Localized restriction equals the coefficientwise injection of the actual R_q. -/
theorem genericRestrict_genericFamily (q : K × K) (S : Polynomial (MvPolynomial (Fin 2) K)) :
    genericRestrict q (genericFamily S) =
      (SlopeSubstitution.pointRestriction q S).map (algebraMap (Polynomial K) (RatFunc K)) := by
  have hhom : (genericRestrict q).toRingHom.comp genericFamily =
      (Polynomial.mapRingHom (algebraMap (Polynomial K) (RatFunc K))).comp
        (SlopeSubstitution.pointRestriction q) := by
    apply Polynomial.ringHom_ext
    · intro F
      simp only [RingHom.comp_apply, genericFamily_C, SlopeSubstitution.pointRestriction,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      exact restrict_planeToUZ q F
    · simp [genericFamily_X, genericRestrict, SlopeSubstitution.pointRestriction]
  exact RingHom.congr_fun hhom S

/-- The exceptional zero restrictions are exactly the same before and after localization. -/
theorem genericRestrict_eq_zero_iff (q : K × K) (S : Polynomial (MvPolynomial (Fin 2) K)) :
    genericRestrict q (genericFamily S) = 0 ↔ SlopeSubstitution.pointRestriction q S = 0 := by
  rw [genericRestrict_genericFamily]
  exact (Polynomial.map_injective _ (RatFunc.algebraMap_injective K)).eq_iff' (by simp)

/-- The precise incidence-forced exponent survives localization. -/
theorem X_pow_incidence_sub_dvd (q : K × K) (L : Finset (K × K))
    (S : Polynomial (MvPolynomial (Fin 2) K)) {e : ℕ} (he : S.natDegree ≤ e)
    (hl : ∀ l ∈ L, FamilySpace.graphRestrict l.1 l.2 (S.eval (MvPolynomial.C l.1)) = 0) :
    Polynomial.X ^ (IncidenceCounting.degree L IncidenceCounting.onGraph q - e) ∣
      genericRestrict q (genericFamily S) := by
  rw [genericRestrict_genericFamily]
  simpa using map_dvd (Polynomial.mapRingHom (algebraMap (Polynomial K) (RatFunc K)))
    (SlopeSubstitution.X_pow_incidence_sub_dvd q L S he hl)

/-- A nonzero pure-z factor becomes a unit here, at localization, and not earlier. -/
theorem pure_slope_isUnit (p : Polynomial K) (hp : p ≠ 0) :
    IsUnit (genericFamily (p.map MvPolynomial.C)) := by
  have heq : genericFamily (p.map MvPolynomial.C) =
      MvPolynomial.C (algebraMap (Polynomial K) (RatFunc K) p) := by
    clear hp
    induction p using Polynomial.induction_on' with
    | add p r hp hr => simp [hp, hr]
    | monomial n c =>
      simp [← Polynomial.C_mul_X_pow_eq_monomial, genericFamily_C]
  rw [heq]
  exact (Ne.isUnit (RatFunc.algebraMap_ne_zero hp)).map MvPolynomial.C

end MathCollab.GenericSlope

#print axioms MathCollab.GenericSlope.genericFamily_injective
#print axioms MathCollab.GenericSlope.genericFamily_squarefree
#print axioms MathCollab.GenericSlope.genericFamily_totalDegree_le
#print axioms MathCollab.GenericSlope.characteristic_bound

#print axioms MathCollab.GenericSlope.intercept_injective
#print axioms MathCollab.GenericSlope.genericRestrict_genericFamily
#print axioms MathCollab.GenericSlope.genericRestrict_eq_zero_iff
#print axioms MathCollab.GenericSlope.X_pow_incidence_sub_dvd
#print axioms MathCollab.GenericSlope.pure_slope_isUnit
