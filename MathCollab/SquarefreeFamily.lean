module
public import MathCollab.SlopeSubstitution
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

@[expose] public section

/-! Squarefree replacement before localizing the slope variable.
Reordering K[x,y][z] as K[z][x,y] makes the plane degree an ordinary total degree,
so divisors preserve it as well as the separate z-degree. -/

noncomputable section
open Classical

namespace MathCollab.SquarefreeFamily

variable {K : Type*} [Field K]

/-- The same polynomial, with z moved into the coefficient ring. -/
def reorder : Polynomial (MvPolynomial (Fin 2) K) ≃ₐ[K] MvPolynomial (Fin 2) (Polynomial K) :=
  (MvPolynomial.optionEquivLeft K (Fin 2)).symm.trans (MvPolynomial.optionEquivRight K (Fin 2))

@[simp] theorem reorder_X : reorder (Polynomial.X : Polynomial (MvPolynomial (Fin 2) K)) =
    MvPolynomial.C Polynomial.X := by
  simp [reorder]

@[simp] theorem reorder_C (F : MvPolynomial (Fin 2) K) :
    reorder (Polynomial.C F) = MvPolynomial.map Polynomial.C F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [reorder]
  | add F G hF hG => simp only [map_add, hF, hG]
  | mul_X F i hF =>
    rw [map_mul, map_mul, hF, map_mul]
    congr 1
    simp [reorder]

/-- Reordering literally transposes the two coefficient indices. -/
theorem coeff_reorder (S : Polynomial (MvPolynomial (Fin 2) K)) (s : Fin 2 →₀ ℕ) (j : ℕ) :
    ((reorder S).coeff s).coeff j = (S.coeff j).coeff s := by
  induction S using Polynomial.induction_on' with
  | add F G hF hG => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Polynomial.coeff_add, hF, hG]
  | monomial n F =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, reorder_C, reorder_X,
      ← map_pow MvPolynomial.C]
    rw [mul_comm (MvPolynomial.map Polynomial.C F) _, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_map, mul_comm]
    by_cases hj : j = n <;> simp [hj]

/-- The original coefficientwise plane bound is exactly total degree after reordering. -/
theorem totalDegree_reorder_le_iff (S : Polynomial (MvPolynomial (Fin 2) K)) (d : ℕ) :
    (reorder S).totalDegree ≤ d ↔ ∀ j, (S.coeff j).totalDegree ≤ d := by
  constructor
  · intro h j
    rw [MvPolynomial.totalDegree]
    apply Finset.sup_le
    intro s hs
    have hs' : s ∈ (reorder S).support := by
      rw [MvPolynomial.mem_support_iff]
      intro hz
      have hcoeff := congrArg (fun P : Polynomial K => P.coeff j) hz
      rw [coeff_reorder, Polynomial.coeff_zero] at hcoeff
      exact (MvPolynomial.mem_support_iff.mp hs) hcoeff
    exact (MvPolynomial.le_totalDegree hs').trans h
  · intro h
    rw [MvPolynomial.totalDegree]
    apply Finset.sup_le
    intro s hs
    have hnz := MvPolynomial.mem_support_iff.mp hs
    have hex : ∃ j, ((reorder S).coeff s).coeff j ≠ 0 := by
      by_contra! hall
      exact hnz (Polynomial.ext fun j => by simpa using hall j)
    obtain ⟨j, hj⟩ := hex
    rw [coeff_reorder] at hj
    exact (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hj)).trans (h j)

/-- Divisibility preserves the exact coefficientwise plane bound, without adding z-degree. -/
theorem coeff_totalDegree_le_of_dvd {S T : Polynomial (MvPolynomial (Fin 2) K)}
    (hS : S ≠ 0) (hTS : T ∣ S) {d : ℕ} (hd : ∀ j, (S.coeff j).totalDegree ≤ d) :
    ∀ j, (T.coeff j).totalDegree ≤ d := by
  apply (totalDegree_reorder_le_iff T d).mp
  have hnz : reorder S ≠ 0 := fun h => hS (reorder.injective (h.trans (map_zero reorder).symm))
  exact (MvPolynomial.totalDegree_le_of_dvd_of_isDomain (map_dvd reorder hTS) hnz).trans
    ((totalDegree_reorder_le_iff S d).mpr hd)

/-- The reverse power divisibility, not divisorhood alone, preserves zero images. -/
theorem map_eq_zero_of_dvd_pow {A B : Type*} [CommRing A] [CommRing B] [IsDomain B]
    (f : A →+* B) {S T : A} {n : ℕ} (hST : S ∣ T ^ n) (hzero : f S = 0) : f T = 0 := by
  have h := map_dvd f hST
  rw [hzero, map_pow, zero_dvd_iff] at h
  exact eq_zero_of_pow_eq_zero h

/-- Squarefree replacement preserves nonzeroness, both degree bounds, and every zero
image in any domain. Pure-z factors have not been discarded or inverted. -/
theorem exists_squarefree_replacement (S : Polynomial (MvPolynomial (Fin 2) K))
    (hS : S ≠ 0) {d e : ℕ} (he : S.natDegree ≤ e)
    (hd : ∀ j, (S.coeff j).totalDegree ≤ d) :
    ∃ T : Polynomial (MvPolynomial (Fin 2) K), T ≠ 0 ∧ Squarefree T ∧ T ∣ S ∧
      (∃ n : ℕ, S ∣ T ^ n) ∧ T.natDegree ≤ e ∧ ∀ j, (T.coeff j).totalDegree ≤ d := by
  obtain ⟨T, n, hsq, hTS, hST⟩ := exists_squarefree_dvd_pow_of_ne_zero hS
  refine ⟨T, ?_, hsq, hTS, ⟨n, hST⟩, ?_, coeff_totalDegree_le_of_dvd hS hTS hd⟩
  · intro hz
    rw [hz, zero_dvd_iff] at hTS
    exact hS hTS
  · exact (Polynomial.natDegree_le_of_dvd hTS hS).trans he

/-- The exact-floor family can be chosen squarefree before applying point substitution. -/
theorem exists_squarefree_family (L : Finset (K × K)) (d : ℕ) :
    ∃ S : Polynomial (MvPolynomial (Fin 2) K), S ≠ 0 ∧ Squarefree S ∧
      S.natDegree ≤ IncidenceOptimization.slopeHeight L.card d ∧
      (∀ j, (S.coeff j).totalDegree ≤ d) ∧
      ∀ l ∈ L, FamilySpace.graphRestrict l.1 l.2 (S.eval (MvPolynomial.C l.1)) = 0 := by
  obtain ⟨S, hS, he, hd, hl⟩ := FamilySpace.exists_family_with_floor L d
  obtain ⟨T, hT, hsq, _, ⟨n, hST⟩, heT, hdT⟩ := exists_squarefree_replacement S hS he hd
  refine ⟨T, hT, hsq, heT, hdT, ?_⟩
  intro l hlL
  exact map_eq_zero_of_dvd_pow
    ((FamilySpace.graphRestrict l.1 l.2).toRingHom.comp (Polynomial.evalRingHom (MvPolynomial.C l.1)))
    hST (hl l hlL)

end MathCollab.SquarefreeFamily

#print axioms MathCollab.SquarefreeFamily.totalDegree_reorder_le_iff
#print axioms MathCollab.SquarefreeFamily.coeff_totalDegree_le_of_dvd
#print axioms MathCollab.SquarefreeFamily.map_eq_zero_of_dvd_pow
#print axioms MathCollab.SquarefreeFamily.exists_squarefree_replacement
#print axioms MathCollab.SquarefreeFamily.exists_squarefree_family
