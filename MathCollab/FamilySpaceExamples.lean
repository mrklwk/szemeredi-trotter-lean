module
public import MathCollab.FamilySpace
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! Empty, zero slope-degree, cancellation, and finite-characteristic family checks. -/

noncomputable section
open Classical MathCollab.FamilySpace

variable {K : Type*} [Field K]

-- No selected lines, d=0, e=0: a nonzero constant family exists.
example : ∃ S : Polynomial (MvPolynomial (Fin 2) K), S ≠ 0 ∧ S.natDegree ≤ 0 ∧
    ∀ j, (S.coeff j).totalDegree ≤ 0 := by
  simpa [MathCollab.IncidenceOptimization.slopeHeight] using
    exists_family_with_floor (∅ : Finset (K × K)) 0

-- One line and d=1 give the exact floor e=0, not an unnecessarily positive cutoff.
example (a b : K) : ∃ S : Polynomial (MvPolynomial (Fin 2) K), S ≠ 0 ∧ S.natDegree ≤ 0 ∧
    (∀ j, (S.coeff j).totalDegree ≤ 1) ∧
    graphRestrict a b (S.eval (MvPolynomial.C a)) = 0 := by
  simpa [MathCollab.IncidenceOptimization.slopeHeight] using
    exists_family_with_floor {(a, b)} 1

-- Substitution can cancel the entire plane polynomial; only an upper degree bound is valid.
example (a b : K) : graphRestrict a b
    (MvPolynomial.X 1 - MvPolynomial.C a * MvPolynomial.X 0 - MvPolynomial.C b) = 0 := by
  simp [graphRestrict]

-- All four graph lines over F₂ at d=1: the exact slope cutoff is e=floor(8/3)=2.
-- e is not required to be below the characteristic or below the plane degree.
example : ∃ S : Polynomial (MvPolynomial (Fin 2) (ZMod 2)), S ≠ 0 ∧ S.natDegree ≤ 2 ∧
    (∀ j, (S.coeff j).totalDegree ≤ 1) ∧
    ∀ l : ZMod 2 × ZMod 2, graphRestrict l.1 l.2 (S.eval (MvPolynomial.C l.1)) = 0 := by
  simpa [MathCollab.IncidenceOptimization.slopeHeight] using
    exists_family_with_floor (Finset.univ : Finset (ZMod 2 × ZMod 2)) 1

-- Audited APIs reused additively from Claude retain only standard dependencies.
#print axioms MathCollab.finrank_degSpace
#print axioms MathCollab.mulSpace_inf_mulSpace
#print axioms MathCollab.finrank_mulSpace_sup_add_mul
