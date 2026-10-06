module
public import MathCollab.IncidenceCounting
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

/-! Finite slopes force vanishing order (arXiv:2609.27023v2, Section 4).
`R : Polynomial (Polynomial K)` has outer variable u and inner variable z.
Coefficient-degree bounds and polynomial specialization identities are explicit
inputs; their derivation from the original family S is a separate obligation. -/

noncomputable section
open Classical

namespace MathCollab.SlopeForcing

variable {K : Type*} [Field K]

/-- Substitute z=a while retaining the outer polynomial variable u. -/
def specializeSlope (R : Polynomial (Polynomial K)) (a : K) : Polynomial K :=
  R.map (Polynomial.evalRingHom a)

theorem coeff_specializeSlope (R : Polynomial (Polynomial K)) (a : K) (j : ℕ) :
    (specializeSlope R a).coeff j = (R.coeff j).eval a := by
  simp [specializeSlope]

/-- More distinct slope roots than the coefficient degree force that coefficient to zero. -/
theorem coeff_eq_zero_of_many_slopes (R : Polynomial (Polynomial K)) (A : Finset K)
    (e j : ℕ) (hdegree : (R.coeff j).natDegree ≤ e + j)
    (hzero : ∀ a ∈ A, specializeSlope R a = 0) (hj : j < A.card - e) :
    R.coeff j = 0 := by
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (R.coeff j) A
  · intro a ha
    have h := congrArg (fun Q : Polynomial K => Q.coeff j) (hzero a ha)
    simpa only [coeff_specializeSlope, Polynomial.coeff_zero] using h
  · omega

/-- The exact forced exponent is natural subtraction |A|−e, over every field. -/
theorem X_pow_card_sub_dvd (R : Polynomial (Polynomial K)) (A : Finset K) (e : ℕ)
    (hdegree : ∀ j, (R.coeff j).natDegree ≤ e + j)
    (hzero : ∀ a ∈ A, specializeSlope R a = 0) :
    Polynomial.X ^ (A.card - e) ∣ R := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro j hj
  exact coeff_eq_zero_of_many_slopes R A e j (hdegree j) hzero hj

/-- A u-degree bound supplies all coefficients above d; only j≤d need input bounds. -/
theorem X_pow_card_sub_dvd_of_natDegree_le (R : Polynomial (Polynomial K))
    (A : Finset K) (e d : ℕ) (hR : R.natDegree ≤ d)
    (hdegree : ∀ j, j ≤ d → (R.coeff j).natDegree ≤ e + j)
    (hzero : ∀ a ∈ A, specializeSlope R a = 0) :
    Polynomial.X ^ (A.card - e) ∣ R := by
  apply X_pow_card_sub_dvd R A e _ hzero
  intro j
  by_cases hj : j ≤ d
  · exact hdegree j hj
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : R.natDegree < j)]
    simp

/-- If the forced exponent exceeds the u-degree, the whole restriction is zero. -/
theorem eq_zero_of_forced_order_gt_degree (R : Polynomial (Polynomial K))
    (A : Finset K) (e d : ℕ) (hR : R.natDegree ≤ d)
    (hdegree : ∀ j, j ≤ d → (R.coeff j).natDegree ≤ e + j)
    (hzero : ∀ a ∈ A, specializeSlope R a = 0) (hlt : d < A.card - e) : R = 0 := by
  by_contra hne
  have h := Polynomial.natDegree_le_of_dvd
    (X_pow_card_sub_dvd_of_natDegree_le R A e d hR hdegree hzero) hne
  simp only [Polynomial.natDegree_X_pow] at h
  omega

open MathCollab.IncidenceCounting

/-- A finite set of distinct slopes of selected graph lines through q. -/
def incidentSlopes (q : K × K) (L : Finset (GraphLine K)) : Finset K :=
  (L.filter (onGraph q)).image Prod.fst

/-- At a fixed point, two normalized graph lines with the same slope coincide. -/
theorem slope_injective_on_incident (q : K × K) (L : Finset (GraphLine K)) :
    Set.InjOn Prod.fst (L.filter (onGraph q) : Set (GraphLine K)) := by
  intro l hl k hk heq
  have hlq := (Finset.mem_filter.mp hl).2
  have hkq := (Finset.mem_filter.mp hk).2
  change q.2 = l.1 * q.1 + l.2 at hlq
  change q.2 = k.1 * q.1 + k.2 at hkq
  apply Prod.ext heq
  change l.1 = k.1 at heq
  rw [heq] at hlq
  linear_combination hkq - hlq

/-- Slope cardinality agrees exactly with the existing incidence degree r(q). -/
theorem incidentSlopes_card (q : K × K) (L : Finset (GraphLine K)) :
    (incidentSlopes q L).card = degree L onGraph q := by
  exact Finset.card_image_of_injOn (slope_injective_on_incident q L)

/-- Graph-line version of the paper's u^(r(q)−e) divisibility conclusion. -/
theorem X_pow_incidence_sub_dvd (R : Polynomial (Polynomial K))
    (q : K × K) (L : Finset (GraphLine K)) (e d : ℕ) (hR : R.natDegree ≤ d)
    (hdegree : ∀ j, j ≤ d → (R.coeff j).natDegree ≤ e + j)
    (hzero : ∀ l ∈ L, onGraph q l → specializeSlope R l.1 = 0) :
    Polynomial.X ^ (degree L onGraph q - e) ∣ R := by
  rw [← incidentSlopes_card q L]
  apply X_pow_card_sub_dvd_of_natDegree_le R (incidentSlopes q L) e d hR hdegree
  intro a ha
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp ha
  exact hzero l (Finset.mem_filter.mp hl).1 (Finset.mem_filter.mp hl).2

end MathCollab.SlopeForcing

#print axioms MathCollab.SlopeForcing.X_pow_card_sub_dvd
#print axioms MathCollab.SlopeForcing.X_pow_card_sub_dvd_of_natDegree_le
#print axioms MathCollab.SlopeForcing.eq_zero_of_forced_order_gt_degree
#print axioms MathCollab.SlopeForcing.incidentSlopes_card
#print axioms MathCollab.SlopeForcing.X_pow_incidence_sub_dvd
