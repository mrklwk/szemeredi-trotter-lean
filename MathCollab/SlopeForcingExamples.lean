module
public import MathCollab.SlopeForcing
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! Boundary checks, including a nonzero polynomial family vanishing at every F₂ slope. -/

noncomputable section
open Classical MathCollab.SlopeForcing MathCollab.IncidenceCounting

variable {K : Type*} [Field K]

-- Zero restrictions are allowed; no finite order of the zero polynomial is used.
example (A : Finset K) (e : ℕ) :
    Polynomial.X ^ (A.card - e) ∣ (0 : Polynomial (Polynomial K)) := by
  apply X_pow_card_sub_dvd _ A e
  · intro j; simp
  · intro a _; simp [specializeSlope]

-- Empty slope set: the exponent is zero for every e.
example (R : Polynomial (Polynomial K)) (e : ℕ)
    (hdegree : ∀ j, (R.coeff j).natDegree ≤ e + j) :
    Polynomial.X ^ ((∅ : Finset K).card - e) ∣ R :=
  X_pow_card_sub_dvd R ∅ e hdegree (by simp)

-- R(u,z)=u(z²-z) has coefficient-degree bound e+j with e=1.
private def testFamily (K : Type*) [Field K] : Polynomial (Polynomial K) :=
  Polynomial.monomial 1 ((Polynomial.X : Polynomial K) ^ 2 - Polynomial.X)

private theorem testFamily_degree (j : ℕ) :
    ((testFamily K).coeff j).natDegree ≤ 1 + j := by
  by_cases hj : 1 = j
  · subst j
    rw [testFamily, Polynomial.coeff_monomial_same]
    exact (Polynomial.natDegree_sub_le _ _).trans (by norm_num)
  · simp [testFamily, Polynomial.coeff_monomial, hj]

private theorem testFamily_zero_on_two (a : K) (ha : a ∈ ({0, 1} : Finset K)) :
    specializeSlope (testFamily K) a = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl <;> simp [specializeSlope, testFamily]

private theorem testFamily_ne_zero : testFamily K ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun R : Polynomial (Polynomial K) => (R.coeff 1).coeff 2) h
  simp [testFamily, Polynomial.coeff_X] at hcoeff

-- Two distinct roots force u^(2-1), over any field, including characteristic two.
example : Polynomial.X ∣ testFamily K := by
  simpa using X_pow_card_sub_dvd (testFamily K) {0, 1} 1 testFamily_degree
    testFamily_zero_on_two

-- The exponent cannot in general be increased: this family is not divisible by u².
example : ¬ Polynomial.X ^ 2 ∣ testFamily K := by
  intro h
  have hle := Polynomial.natDegree_le_of_dvd h (testFamily_ne_zero (K := K))
  have hdeg : (testFamily K).natDegree ≤ 1 := Polynomial.natDegree_monomial_le _
  simp only [Polynomial.natDegree_X_pow] at hle
  omega

-- A finite field's entire set of slope evaluations can vanish without R being zero.
example (a : ZMod 2) : specializeSlope (testFamily (ZMod 2)) a = 0 := by
  fin_cases a <;> simp [specializeSlope, testFamily]

example : testFamily (ZMod 2) ≠ 0 := testFamily_ne_zero

-- Three selected graph lines have only two incidences at the origin; the second
-- line of slope one misses the point, so it must not create a duplicate slope.
example : incidentSlopes ((0, 0) : ℚ × ℚ) {(0, 0), (1, 0), (1, 1)} = {0, 1} := by
  simp [incidentSlopes, onGraph, Finset.filter_insert, Finset.filter_singleton]
  ext x
  simp

-- Only coefficients j≤d are required even if the forced exponent exceeds d.
example (R : Polynomial (Polynomial K)) (A : Finset K) (e : ℕ)
    (hR : R.natDegree ≤ 0) (hcoeff : (R.coeff 0).natDegree ≤ e)
    (hzero : ∀ a ∈ A, specializeSlope R a = 0) (hA : e < A.card) : R = 0 := by
  apply eq_zero_of_forced_order_gt_degree R A e 0 hR _ hzero (by omega)
  intro j hj
  have : j = 0 := by omega
  subst j
  simpa using hcoeff
