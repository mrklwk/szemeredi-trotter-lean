module
public import MathCollab.FamilySpace
public import MathCollab.SlopeForcing

@[expose] public section

/-! Actual point substitution for the bounded family from Section 4.
The input is a polynomial in z with coefficients in K[x,y]; the output has
outer variable u and inner variable z. Both degree bounds and all identities
are polynomial statements over an arbitrary field, including finite fields. -/

noncomputable section
open Classical
open scoped BigOperators

namespace MathCollab.SlopeSubstitution

variable {K : Type*} [Field K]

/-- Coefficient j has z-degree at most e+j. -/
def CoeffBound (e : ℕ) (R : Polynomial (Polynomial K)) : Prop :=
  ∀ j, (R.coeff j).natDegree ≤ e + j

theorem CoeffBound.mono {e f : ℕ} {R : Polynomial (Polynomial K)}
    (h : CoeffBound e R) (hef : e ≤ f) : CoeffBound f R :=
  fun j => (h j).trans (Nat.add_le_add_right hef j)

theorem coeffBound_zero (e : ℕ) : CoeffBound e (0 : Polynomial (Polynomial K)) := by
  intro j
  simp

theorem coeffBound_C {e : ℕ} (p : Polynomial K) (hp : p.natDegree ≤ e) :
    CoeffBound e (Polynomial.C p) := by
  intro j
  by_cases hj : j = 0
  · simpa [hj] using hp
  · simp [Polynomial.coeff_C, hj]

theorem CoeffBound.add {e : ℕ} {R T : Polynomial (Polynomial K)}
    (hR : CoeffBound e R) (hT : CoeffBound e T) : CoeffBound e (R + T) := by
  intro j
  rw [Polynomial.coeff_add]
  exact (Polynomial.natDegree_add_le _ _).trans (max_le (hR j) (hT j))

theorem CoeffBound.mul {e f : ℕ} {R T : Polynomial (Polynomial K)}
    (hR : CoeffBound e R) (hT : CoeffBound f T) : CoeffBound (e + f) (R * T) := by
  intro j
  rw [Polynomial.coeff_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro ij hij
  have hsum := Finset.mem_antidiagonal.mp hij
  exact Polynomial.natDegree_mul_le.trans (by have := hR ij.1; have := hT ij.2; omega)

theorem coeffBound_one : CoeffBound 0 (1 : Polynomial (Polynomial K)) := by
  simpa using coeffBound_C (1 : Polynomial K) (by simp : (1 : Polynomial K).natDegree ≤ 0)

theorem CoeffBound.pow {e : ℕ} {R : Polynomial (Polynomial K)}
    (hR : CoeffBound e R) (n : ℕ) : CoeffBound (n * e) (R ^ n) := by
  induction n with
  | zero => simpa using coeffBound_one (K := K)
  | succ n ih => simpa [pow_succ, Nat.succ_mul] using ih.mul hR

theorem coeffBound_X : CoeffBound 0 (Polynomial.X : Polynomial (Polynomial K)) := by
  intro j
  by_cases hj : 1 = j <;> simp [Polynomial.coeff_X, hj]

/-- Substitute x=q₁+u and y=q₂+zu into a plane polynomial. -/
def planeToUZ (q : K × K) : MvPolynomial (Fin 2) K →ₐ[K] Polynomial (Polynomial K) :=
  MvPolynomial.aeval ![Polynomial.C (Polynomial.C q.1) + Polynomial.X,
    Polynomial.C (Polynomial.C q.2) + Polynomial.C Polynomial.X * Polynomial.X]

/-- The actual polynomial R_q(u,z)=S(q₁+u,q₂+zu,z). -/
def pointRestriction (q : K × K) :
    Polynomial (MvPolynomial (Fin 2) K) →+* Polynomial (Polynomial K) :=
  Polynomial.eval₂RingHom (planeToUZ q).toRingHom (Polynomial.C Polynomial.X)

theorem coeffBound_planeToUZ (q : K × K) (F : MvPolynomial (Fin 2) K) :
    CoeffBound 0 (planeToUZ q F) := by
  have hconst (c : K) : CoeffBound 0 (Polynomial.C (Polynomial.C c)) :=
    coeffBound_C _ (by simp)
  have hvar (i : Fin 2) : CoeffBound 0 (planeToUZ q (MvPolynomial.X i)) := by
    fin_cases i
    · simpa [planeToUZ] using (hconst q.1).add coeffBound_X
    · have hzu : CoeffBound 0 (Polynomial.C Polynomial.X * Polynomial.X :
          Polynomial (Polynomial K)) := by
        intro j
        by_cases hj : 1 = j
        · subst j; simp
        · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X, hj]
      simpa [planeToUZ] using (hconst q.2).add hzu
  induction F using MvPolynomial.induction_on with
  | C c => simpa [planeToUZ, Polynomial.algebraMap_eq] using hconst c
  | add F G hF hG => simpa only [map_add] using hF.add hG
  | mul_X F i hF => simpa only [map_mul, Nat.add_zero] using hF.mul (hvar i)

/-- The coefficient-degree estimate e+j follows from the actual substitution. -/
theorem pointRestriction_coeff_natDegree_le (q : K × K)
    (S : Polynomial (MvPolynomial (Fin 2) K)) {e : ℕ} (he : S.natDegree ≤ e) :
    CoeffBound e (pointRestriction q S) := by
  intro j
  change ((S.eval₂ (planeToUZ q).toRingHom (Polynomial.C Polynomial.X)).coeff j).natDegree ≤ e + j
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum, Polynomial.finsetSum_coeff]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro γ hγ
  have hz : CoeffBound 1 (Polynomial.C Polynomial.X : Polynomial (Polynomial K)) :=
    coeffBound_C _ (by simp)
  have hterm := (coeffBound_planeToUZ q (S.coeff γ)).mul (hz.pow γ)
  have hγe : γ ≤ e := (Polynomial.le_natDegree_of_mem_supp γ hγ).trans he
  exact (hterm j).trans (by omega)

theorem planeToUZ_monomial (q : K × K) (s : Fin 2 →₀ ℕ) (c : K) :
    planeToUZ q (MvPolynomial.monomial s c) =
      Polynomial.C (Polynomial.C c) *
        ((Polynomial.C (Polynomial.C q.1) + Polynomial.X) ^ s 0 *
          (Polynomial.C (Polynomial.C q.2) + Polynomial.C Polynomial.X * Polynomial.X) ^ s 1) := by
  simp [planeToUZ, MvPolynomial.aeval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two,
    Polynomial.algebraMap_eq]

/-- The plane substitution is affine in u, so its u-degree cannot exceed plane degree. -/
theorem planeToUZ_natDegree_le (q : K × K) (F : MvPolynomial (Fin 2) K) :
    (planeToUZ q F).natDegree ≤ F.totalDegree := by
  have hlinear (i : Fin 2) : (planeToUZ q (MvPolynomial.X i)).natDegree ≤ 1 := by
    fin_cases i
    · simp only [planeToUZ, MvPolynomial.aeval_X]
      exact (Polynomial.natDegree_add_le _ _).trans (by simp)
    · simp only [planeToUZ, MvPolynomial.aeval_X]
      apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le (by simp)
      exact Polynomial.natDegree_mul_le.trans (by simp)
  conv_lhs => rw [F.as_sum, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s hs
  rw [planeToUZ_monomial]
  apply Polynomial.natDegree_mul_le.trans
  simp only [Polynomial.natDegree_C, zero_add]
  apply Polynomial.natDegree_mul_le.trans
  have h0 := hlinear 0
  have h1 := hlinear 1
  simp only [planeToUZ, MvPolynomial.aeval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one] at h0 h1
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_pow]
  apply (Nat.add_le_add (Nat.mul_le_mul_left (s 0) h0)
    (Nat.mul_le_mul_left (s 1) h1)).trans
  simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using MvPolynomial.le_totalDegree hs

/-- The separate plane-degree bound d becomes a u-degree bound d. -/
theorem pointRestriction_natDegree_le (q : K × K)
    (S : Polynomial (MvPolynomial (Fin 2) K)) {d : ℕ}
    (hd : ∀ j, (S.coeff j).totalDegree ≤ d) :
    (pointRestriction q S).natDegree ≤ d := by
  change (S.eval₂ (planeToUZ q).toRingHom (Polynomial.C Polynomial.X)).natDegree ≤ d
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  apply Polynomial.natDegree_mul_le.trans
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Polynomial.natDegree_pow, Polynomial.natDegree_C, mul_zero, add_zero]
  exact (planeToUZ_natDegree_le q (S.coeff j)).trans (hd j)

/-- Specializing the slope gives restriction to the incident graph line,
with the parameter shifted so u=0 corresponds to q. -/
theorem specialize_planeToUZ (q : K × K) (a b : K)
    (hq : q.2 = a * q.1 + b) (F : MvPolynomial (Fin 2) K) :
    SlopeForcing.specializeSlope (planeToUZ q F) a =
      (FamilySpace.graphRestrict a b F).comp (Polynomial.C q.1 + Polynomial.X) := by
  change (Polynomial.mapRingHom (Polynomial.evalRingHom a)) (planeToUZ q F) =
    (Polynomial.compRingHom (Polynomial.C q.1 + Polynomial.X)) (FamilySpace.graphRestrict a b F)
  induction F using MvPolynomial.induction_on with
  | C c => simp [planeToUZ, FamilySpace.graphRestrict, Polynomial.algebraMap_eq]
  | add F G hF hG => simp only [map_add, hF, hG]
  | mul_X F i hF =>
    simp only [map_mul, hF]
    congr 1
    fin_cases i
    · simp [planeToUZ, FamilySpace.graphRestrict]
    · simp [planeToUZ, FamilySpace.graphRestrict, hq, Polynomial.C_add, Polynomial.C_mul]
      ring

/-- A polynomial identity for S on an incident line is an identity for R_q at that slope. -/
theorem specialize_pointRestriction (q : K × K) (a b : K)
    (hq : q.2 = a * q.1 + b) (S : Polynomial (MvPolynomial (Fin 2) K)) :
    SlopeForcing.specializeSlope (pointRestriction q S) a =
      (FamilySpace.graphRestrict a b (S.eval (MvPolynomial.C a))).comp
        (Polynomial.C q.1 + Polynomial.X) := by
  have hhom : (Polynomial.mapRingHom (Polynomial.evalRingHom a)).comp (pointRestriction q) =
      (Polynomial.compRingHom (Polynomial.C q.1 + Polynomial.X)).comp
        ((FamilySpace.graphRestrict a b).toRingHom.comp (Polynomial.evalRingHom (MvPolynomial.C a))) := by
    apply Polynomial.ringHom_ext
    · intro F
      simp only [RingHom.comp_apply, pointRestriction, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C, Polynomial.coe_evalRingHom, Polynomial.eval_C]
      change SlopeForcing.specializeSlope (planeToUZ q F) a =
        (FamilySpace.graphRestrict a b F).comp (Polynomial.C q.1 + Polynomial.X)
      exact specialize_planeToUZ q a b hq F
    · simp only [RingHom.comp_apply, pointRestriction, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X, Polynomial.coe_evalRingHom, Polynomial.eval_X]
      change SlopeForcing.specializeSlope (Polynomial.C Polynomial.X) a =
        (FamilySpace.graphRestrict a b (MvPolynomial.C a)).comp (Polynomial.C q.1 + Polynomial.X)
      simp [SlopeForcing.specializeSlope, FamilySpace.graphRestrict]
  exact RingHom.congr_fun hhom S

open MathCollab.IncidenceCounting

/-- All inputs to finite-root forcing are now proved for the actual family substitution. -/
theorem X_pow_incidence_sub_dvd (q : K × K) (L : Finset (GraphLine K))
    (S : Polynomial (MvPolynomial (Fin 2) K)) {e : ℕ} (he : S.natDegree ≤ e)
    (hlines : ∀ l ∈ L, FamilySpace.graphRestrict l.1 l.2 (S.eval (MvPolynomial.C l.1)) = 0) :
    Polynomial.X ^ (degree L onGraph q - e) ∣ pointRestriction q S := by
  rw [← SlopeForcing.incidentSlopes_card q L]
  apply SlopeForcing.X_pow_card_sub_dvd _ _ e (pointRestriction_coeff_natDegree_le q S he)
  intro a ha
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨hlL, hlq⟩ := Finset.mem_filter.mp hl
  rw [specialize_pointRestriction q l.1 l.2 hlq S, hlines l hlL]
  simp

/-- The constructed nonzero family with the exact floor cutoff also has the asserted
point-restriction degree bounds and forced powers, over every field. Squarefreeness
and localization are separate later obligations. -/
theorem exists_family_with_point_restrictions (L : Finset (GraphLine K)) (d : ℕ) :
    ∃ S : Polynomial (MvPolynomial (Fin 2) K), S ≠ 0 ∧
      S.natDegree ≤ IncidenceOptimization.slopeHeight L.card d ∧
      (∀ j, (S.coeff j).totalDegree ≤ d) ∧
      (∀ l ∈ L, FamilySpace.graphRestrict l.1 l.2 (S.eval (MvPolynomial.C l.1)) = 0) ∧
      ∀ q : K × K, (pointRestriction q S).natDegree ≤ d ∧
        CoeffBound (IncidenceOptimization.slopeHeight L.card d) (pointRestriction q S) ∧
        Polynomial.X ^ (degree L onGraph q - IncidenceOptimization.slopeHeight L.card d) ∣
          pointRestriction q S := by
  obtain ⟨S, hS, he, hd, hlines⟩ := FamilySpace.exists_family_with_floor L d
  refine ⟨S, hS, he, hd, hlines, fun q => ⟨?_, ?_, ?_⟩⟩
  · exact pointRestriction_natDegree_le q S hd
  · exact pointRestriction_coeff_natDegree_le q S he
  · exact X_pow_incidence_sub_dvd q L S he hlines

end MathCollab.SlopeSubstitution

#print axioms MathCollab.SlopeSubstitution.pointRestriction_coeff_natDegree_le
#print axioms MathCollab.SlopeSubstitution.pointRestriction_natDegree_le
#print axioms MathCollab.SlopeSubstitution.specialize_pointRestriction
#print axioms MathCollab.SlopeSubstitution.X_pow_incidence_sub_dvd
#print axioms MathCollab.SlopeSubstitution.exists_family_with_point_restrictions
