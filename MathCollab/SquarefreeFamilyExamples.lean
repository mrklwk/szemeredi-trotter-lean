module
public import MathCollab.SquarefreeFamily
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

noncomputable section
open Classical
open MathCollab.SquarefreeFamily

namespace MathCollab.SquarefreeFamilyExamples

-- Empty lines and d=0 are permitted; no hidden d≥1 or characteristic condition.
example : ∃ S : Polynomial (MvPolynomial (Fin 2) (ZMod 2)), S ≠ 0 ∧ Squarefree S ∧
    S.natDegree ≤ 0 ∧ (∀ j, (S.coeff j).totalDegree ≤ 0) ∧
    ∀ l ∈ (∅ : Finset (ZMod 2 × ZMod 2)),
      FamilySpace.graphRestrict l.1 l.2 (S.eval (MvPolynomial.C l.1)) = 0 := by
  simpa [IncidenceOptimization.slopeHeight] using
    exists_squarefree_family (∅ : Finset (ZMod 2 × ZMod 2)) 0

-- In characteristic two, repeated pure-z factors are reduced but not discarded:
-- the replacement still vanishes at z=0 and still has plane degree zero.
theorem pure_slope_replacement :
    ∃ T : Polynomial (MvPolynomial (Fin 2) (ZMod 2)),
      T ≠ 0 ∧ Squarefree T ∧ T.natDegree ≤ 2 ∧
      (∀ j, (T.coeff j).totalDegree ≤ 0) ∧ T.eval 0 = 0 := by
  let S : Polynomial (MvPolynomial (Fin 2) (ZMod 2)) := Polynomial.X ^ 2
  have hS : S ≠ 0 := by simp [S]
  have hd : ∀ j, (S.coeff j).totalDegree ≤ 0 := by
    intro j
    simp only [S, Polynomial.coeff_X_pow]
    split_ifs <;> simp
  obtain ⟨T, hT, hsq, _, ⟨n, hST⟩, heT, hdT⟩ :=
    exists_squarefree_replacement S hS (by simp [S] : S.natDegree ≤ 2) hd
  refine ⟨T, hT, hsq, heT, hdT, ?_⟩
  exact map_eq_zero_of_dvd_pow (Polynomial.evalRingHom 0) hST (by simp [S])

-- A unit input and n=0 in the squarefree existence API cause no exception.
example : ∃ T : Polynomial (MvPolynomial (Fin 2) ℚ), T ≠ 0 ∧ Squarefree T ∧
    T ∣ 1 ∧ (∃ n : ℕ, 1 ∣ T ^ n) ∧ T.natDegree ≤ 0 ∧
    ∀ j, (T.coeff j).totalDegree ≤ 0 := by
  apply exists_squarefree_replacement 1 one_ne_zero (by simp)
  intro j
  by_cases hj : j = 0 <;> simp [Polynomial.coeff_one, hj]

-- Divisorhood by itself has the wrong direction for preserving zero images.
example : (1 : Polynomial ℚ) ∣ Polynomial.X ∧
    (Polynomial.X : Polynomial ℚ).eval 0 = 0 ∧ (1 : Polynomial ℚ).eval 0 ≠ 0 := by
  simp

#print axioms pure_slope_replacement
end MathCollab.SquarefreeFamilyExamples
