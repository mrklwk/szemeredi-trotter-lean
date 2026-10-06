module
public import MathCollab.MultiplicityParallel
public import MathCollab.Exceptional

@[expose] public section

noncomputable section
open Classical
namespace MathCollab.Parameterized
open MathCollab
variable {K : Type*} [Field K]

theorem native_restriction (q : K × K) (F : MvPolynomial (Fin 2) (RatFunc K)) :
    GenericSlope.genericRestrict q F =
      slopeRestrict RatFunc.X (RatFunc.C q.1) (GenericSlope.intercept q) F := by
  simp [GenericSlope.genericRestrict, slopeRestrict, GenericSlope.intercept]

-- Actual inputs now match Claude's audited multiplicity theorem with no new algebraic assumption.
theorem localized_multiplicity {J : Type*} [Fintype J]
    (q : J → K × K) (hq : Function.Injective q) (L : Finset (K × K))
    (S : Polynomial (MvPolynomial (Fin 2) K)) (hS : S ≠ 0) (hsq : Squarefree S)
    {d e : ℕ} (hc : ringChar K = 0 ∨ d < ringChar K)
    (he : S.natDegree ≤ e) (hd : ∀ j, (S.coeff j).totalDegree ≤ d)
    (hl : ∀ l ∈ L, FamilySpace.graphRestrict l.1 l.2 (S.eval (MvPolynomial.C l.1)) = 0)
    (hnz : ∀ i, SlopeSubstitution.pointRestriction (q i) S ≠ 0) :
    ∑ i, (IncidenceCounting.degree L IncidenceCounting.onGraph (q i) - e - 1) ≤ d * (d - 1) := by
  apply sum_sub_one_le_of_squarefree_slope RatFunc.X (fun i => RatFunc.C (q i).1)
    (b := fun i => GenericSlope.intercept (q i)) (GenericSlope.intercept_injective.comp hq)
    (GenericSlope.characteristic_bound hc) (GenericSlope.genericFamily_ne_zero hS)
    (GenericSlope.genericFamily_squarefree hsq hS) (GenericSlope.genericFamily_totalDegree_le S hd)
    (fun i => IncidenceCounting.degree L IncidenceCounting.onGraph (q i) - e)
  · intro i
    rw [← native_restriction]
    exact fun h => hnz i ((GenericSlope.genericRestrict_eq_zero_iff _ _).mp h)
  · intro i
    rw [← native_restriction]
    exact GenericSlope.X_pow_incidence_sub_dvd (q i) L S he hl

#print axioms localized_multiplicity
open IncidenceCounting

/-- Exact normalized graph-plus-vertical discrete bound; all algebraic inputs are proved. -/
theorem discrete_bound (P : Finset (K × K)) (L : Finset (K × K)) (V : Finset K)
    (d : ℕ) (hc : ringChar K = 0 ∨ d < ringChar K) :
    count P L onGraph + count P V (fun q c => q.1 = c) ≤
      P.card * (IncidenceOptimization.slopeHeight L.card d + 2) + d * (d - 1) + L.card := by
  obtain ⟨S, hS, hsq, he, hd, hl⟩ := SquarefreeFamily.exists_squarefree_family L d
  let E := Exceptional.exceptionalSet P S
  have hbudget : (∑ q ∈ P \ E,
      (degree L onGraph q - IncidenceOptimization.slopeHeight L.card d - 1)) ≤ d * (d - 1) := by
    have h := localized_multiplicity (fun q : (P \ E : Finset (K × K)) => (q : K × K)) Subtype.val_injective
      L S hS hsq hc he hd hl
      (fun q => Exceptional.pointRestriction_ne_zero_of_mem_sdiff P S q.property)
    have heq := Finset.sum_coe_sort (P \ E)
      (fun q => degree L onGraph q - IncidenceOptimization.slopeHeight L.card d - 1)
    rw [← heq]
    exact h
  exact graph_vertical_count_le_of_exceptional_budget P E L V _ d
    (Exceptional.exceptionalSet_subset P S) (Exceptional.exceptionalSet_card_le P S hS he) hbudget

#print axioms discrete_bound
end MathCollab.Parameterized
