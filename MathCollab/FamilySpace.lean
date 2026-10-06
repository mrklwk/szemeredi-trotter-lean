module
public import MathCollab.MulSpaces
public import MathCollab.IncidenceOptimization
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Tactic

@[expose] public section

/-! The bounded polynomial family from Section 4 of arXiv:2609.27023v2.
A family is a polynomial in z whose coefficients are bivariate polynomials in x,y.
Plane degree and slope degree remain separate bounds. -/

noncomputable section
open scoped BigOperators
open Classical

namespace MathCollab.FamilySpace

variable {K : Type*} [Field K]

/-- Restrict a plane polynomial to the graph line y=a*x+b. -/
def graphRestrict (a b : K) : MvPolynomial (Fin 2) K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval ![Polynomial.X, Polynomial.C a * Polynomial.X + Polynomial.C b]

theorem graphRestrict_monomial (a b c : K) (s : Fin 2 →₀ ℕ) :
    graphRestrict a b (MvPolynomial.monomial s c) =
      Polynomial.C c * (Polynomial.X ^ s 0 *
        (Polynomial.C a * Polynomial.X + Polynomial.C b) ^ s 1) := by
  simp [graphRestrict, MvPolynomial.aeval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two]

theorem graphRestrict_natDegree_monomial_le (a b c : K) (s : Fin 2 →₀ ℕ) :
    (graphRestrict a b (MvPolynomial.monomial s c)).natDegree ≤ s 0 + s 1 := by
  have hlinear : (Polynomial.C a * Polynomial.X + Polynomial.C b).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · exact Polynomial.natDegree_mul_le.trans (by simp)
    · simp
  rw [graphRestrict_monomial]
  apply Polynomial.natDegree_mul_le.trans
  simp only [Polynomial.natDegree_C, zero_add]
  apply Polynomial.natDegree_mul_le.trans
  simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one]
  simpa using Nat.add_le_add_left (Nat.mul_le_mul_left (s 1) hlinear) (s 0)

/-- A graph-line substitution does not raise total degree. -/
theorem graphRestrict_natDegree_le (a b : K) (F : MvPolynomial (Fin 2) K) :
    (graphRestrict a b F).natDegree ≤ F.totalDegree := by
  conv_lhs => rw [F.as_sum]
  rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s hs
  apply (graphRestrict_natDegree_monomial_le a b (F.coeff s) s).trans
  simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using MvPolynomial.le_totalDegree hs

/-- e+1 coefficients of plane degree at most d. -/
abbrev CoeffSpace (K : Type*) [Field K] (d e : ℕ) := Fin (e + 1) → degSpace K d

theorem finrank_coeffSpace (d e : ℕ) :
    Module.finrank K (CoeffSpace K d e) = (e + 1) * (d + 2).choose 2 := by
  rw [Module.finrank_pi_fintype]
  simp [finrank_degSpace]

/-- Evaluate the z-coefficient vector at z=a, retaining the bounded plane space. -/
def familyAt (d e : ℕ) (a : K) : CoeffSpace K d e →ₗ[K] degSpace K d where
  toFun c := ∑ j : Fin (e + 1), a ^ (j : ℕ) • c j
  map_add' c c' := by simp [smul_add, Finset.sum_add_distrib]
  map_smul' t c := by simp [Finset.smul_sum, smul_smul, mul_comm]

/-- The actual polynomial in z; nonzeroness refers to its coefficients, not evaluations. -/
def familyPolynomial {d e : ℕ} (c : CoeffSpace K d e) : Polynomial (MvPolynomial (Fin 2) K) :=
  ∑ j : Fin (e + 1), Polynomial.monomial (j : ℕ) (c j : MvPolynomial (Fin 2) K)

theorem familyPolynomial_coeff {d e : ℕ} (c : CoeffSpace K d e) (j : Fin (e + 1)) :
    (familyPolynomial c).coeff (j : ℕ) = (c j : MvPolynomial (Fin 2) K) := by
  simp only [familyPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    have hval : (k : ℕ) ≠ (j : ℕ) := fun h => hkj (Fin.ext h)
    simp [hval]
  · simp

theorem familyPolynomial_ne_zero {d e : ℕ} {c : CoeffSpace K d e} (hc : c ≠ 0) :
    familyPolynomial c ≠ 0 := by
  intro h
  apply hc
  funext j
  apply Subtype.ext
  have hcoeff := congrArg (fun S : Polynomial (MvPolynomial (Fin 2) K) => S.coeff (j : ℕ)) h
  simpa only [familyPolynomial_coeff, Polynomial.coeff_zero, Pi.zero_apply, Submodule.coe_zero]
    using hcoeff

theorem familyPolynomial_natDegree_le {d e : ℕ} (c : CoeffSpace K d e) :
    (familyPolynomial c).natDegree ≤ e := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_monomial_le _).trans (by omega)

theorem familyPolynomial_coeff_totalDegree_le {d e : ℕ} (c : CoeffSpace K d e) (j : ℕ) :
    ((familyPolynomial c).coeff j).totalDegree ≤ d := by
  by_cases hj : j < e + 1
  · have h := familyPolynomial_coeff c ⟨j, hj⟩
    rw [h]
    exact mem_degSpace_iff.mp (c ⟨j, hj⟩).property
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (familyPolynomial_natDegree_le c) (by omega))]
    simp

theorem familyPolynomial_eval {d e : ℕ} (c : CoeffSpace K d e) (a : K) :
    (familyPolynomial c).eval (MvPolynomial.C a) =
      (familyAt d e a c : MvPolynomial (Fin 2) K) := by
  simp [familyPolynomial, familyAt, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    MvPolynomial.smul_eq_C_mul, map_pow, mul_comm]

/-- Each selected graph line contributes d+1 coefficient constraints. -/
def constraintMap (L : Finset (K × K)) (d e : ℕ) :
    CoeffSpace K d e →ₗ[K] (L → Fin (d + 1) → K) :=
  LinearMap.pi fun l => LinearMap.pi fun j =>
    (Polynomial.lcoeff K (j : ℕ)).comp
      (((graphRestrict l.1.1 l.1.2).toLinearMap.comp (degSpace K d).subtype).comp
        (familyAt d e l.1.1))

theorem constraintMap_apply (L : Finset (K × K)) (d e : ℕ)
    (c : CoeffSpace K d e) (l : L) (j : Fin (d + 1)) :
    constraintMap L d e c l j =
      (graphRestrict l.1.1 l.1.2 (familyAt d e l.1.1 c)).coeff (j : ℕ) := rfl

theorem finrank_constraints (L : Finset (K × K)) (d : ℕ) :
    Module.finrank K (L → Fin (d + 1) → K) = L.card * (d + 1) := by
  rw [Module.finrank_pi_fintype]
  simp

theorem dimension_inequality (d e n : ℕ) (h : 2 * n < (e + 1) * (d + 2)) :
    n * (d + 1) < (e + 1) * (d + 2).choose 2 := by
  have hmul := Nat.mul_lt_mul_of_pos_right h (by omega : 0 < d + 1)
  have hid := congrArg (fun x : ℕ => (e + 1) * x) (two_mul_choose_add_two d)
  nlinarith

/-- Vanishing of the d+1 constraints is a full polynomial identity, using the degree bound. -/
theorem kernel_line_identity (L : Finset (K × K)) (d e : ℕ) (c : CoeffSpace K d e)
    (hc : constraintMap L d e c = 0) (l : L) :
    graphRestrict l.1.1 l.1.2 (familyAt d e l.1.1 c) = 0 := by
  apply Polynomial.ext
  intro j
  rw [Polynomial.coeff_zero]
  by_cases hj : j < d + 1
  · have h := congrFun (congrFun hc l) ⟨j, hj⟩
    simpa only [constraintMap_apply, Pi.zero_apply] using h
  · have hdeg := (graphRestrict_natDegree_le l.1.1 l.1.2
      (familyAt d e l.1.1 c)).trans (mem_degSpace_iff.mp (familyAt d e l.1.1 c).property)
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-- The nonzero bounded family exists over any field when the coefficient count is strict. -/
theorem exists_family (L : Finset (K × K)) (d e : ℕ)
    (hcount : 2 * L.card < (e + 1) * (d + 2)) :
    ∃ S : Polynomial (MvPolynomial (Fin 2) K), S ≠ 0 ∧ S.natDegree ≤ e ∧
      (∀ j, (S.coeff j).totalDegree ≤ d) ∧
      ∀ l ∈ L, graphRestrict l.1 l.2 (S.eval (MvPolynomial.C l.1)) = 0 := by
  have hdim : Module.finrank K (L → Fin (d + 1) → K) < Module.finrank K (CoeffSpace K d e) := by
    rw [finrank_constraints, finrank_coeffSpace]
    exact dimension_inequality d e L.card hcount
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := constraintMap L d e) hdim
  obtain ⟨c, hc, hc0⟩ := (LinearMap.ker (constraintMap L d e)).ne_bot_iff.mp hker
  change constraintMap L d e c = 0 at hc
  refine ⟨familyPolynomial c, familyPolynomial_ne_zero hc0, familyPolynomial_natDegree_le c,
    familyPolynomial_coeff_totalDegree_le c, ?_⟩
  intro l hl
  rw [familyPolynomial_eval]
  exact kernel_line_identity L d e c hc ⟨l, hl⟩

/-- The paper's exact floor e=floor(2*n₀/(d+2)) always supplies enough coefficients. -/
theorem exists_family_with_floor (L : Finset (K × K)) (d : ℕ) :
    ∃ S : Polynomial (MvPolynomial (Fin 2) K), S ≠ 0 ∧
      S.natDegree ≤ IncidenceOptimization.slopeHeight L.card d ∧
      (∀ j, (S.coeff j).totalDegree ≤ d) ∧
      ∀ l ∈ L, graphRestrict l.1 l.2 (S.eval (MvPolynomial.C l.1)) = 0 :=
  exists_family L d (IncidenceOptimization.slopeHeight L.card d)
    (IncidenceOptimization.slopeHeight_strict L.card d)

end MathCollab.FamilySpace

#print axioms MathCollab.FamilySpace.graphRestrict_natDegree_le
#print axioms MathCollab.FamilySpace.finrank_coeffSpace
#print axioms MathCollab.FamilySpace.exists_family
#print axioms MathCollab.FamilySpace.exists_family_with_floor
