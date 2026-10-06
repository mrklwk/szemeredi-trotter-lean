module
public import MathCollab.GenericSlope
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

/-! Exceptional restrictions and the exact bound |E|≤e.
Over the fraction field of K[x,y], the distinct linear-z factors through q have
roots (y−q₂)/(x−q₁). Root counting gives the same z-degree bound without choosing
values for x,y in the original field. No squarefreeness is required here. -/

noncomputable section
open Classical

namespace MathCollab.Exceptional

variable {K : Type*} [Field K]

abbrev Plane (K : Type*) [Field K] := MvPolynomial (Fin 2) K
abbrev PlaneFraction (K : Type*) [Field K] := FractionRing (Plane K)

def planeEmbed : Plane K →+* PlaneFraction K := algebraMap (Plane K) (PlaneFraction K)

theorem planeEmbed_injective : Function.Injective (planeEmbed (K := K)) :=
  IsFractionRing.injective _ _

theorem X_sub_C_ne_zero (c : K) : (MvPolynomial.X 0 - MvPolynomial.C c : Plane K) ≠ 0 := by
  intro h
  have hc := congrArg (fun F : Plane K => F.coeff (Finsupp.single 0 1)) h
  have h0 : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 1 := by
    intro h
    have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
    simp at this
  simp [MvPolynomial.coeff_X, MvPolynomial.coeff_C, h0] at hc

theorem denominator_ne_zero (q : K × K) :
    planeEmbed (MvPolynomial.X 0 - MvPolynomial.C q.1) ≠ 0 := by
  intro h
  exact X_sub_C_ne_zero q.1 (planeEmbed_injective (h.trans (map_zero planeEmbed).symm))

/-- Root of the auxiliary linear-z factor over the plane's fraction field. -/
def factorRoot (q : K × K) : PlaneFraction K :=
  planeEmbed (MvPolynomial.X 1 - MvPolynomial.C q.2) /
    planeEmbed (MvPolynomial.X 0 - MvPolynomial.C q.1)

/-- The roots of the exceptional factors are distinct for distinct original points. -/
theorem factorRoot_injective : Function.Injective (factorRoot (K := K)) := by
  intro q r h
  have hc := (div_eq_div_iff (denominator_ne_zero q) (denominator_ne_zero r)).mp h
  have hp : (MvPolynomial.X 1 - MvPolynomial.C q.2 : Plane K) * (MvPolynomial.X 0 - MvPolynomial.C r.1) =
      (MvPolynomial.X 1 - MvPolynomial.C r.2) * (MvPolynomial.X 0 - MvPolynomial.C q.1) := by
    apply planeEmbed_injective
    simpa only [map_mul] using hc
  have hlin : MvPolynomial.C (q.1 - r.1) * MvPolynomial.X 1 +
      MvPolynomial.C (r.2 - q.2) * MvPolynomial.X 0 +
      MvPolynomial.C (q.2 * r.1 - r.2 * q.1) = (0 : Plane K) := by
    simp only [map_sub, map_mul]
    linear_combination hp
  have hx := congrArg (fun F : Plane K => F.coeff (Finsupp.single 0 1)) hlin
  have hy := congrArg (fun F : Plane K => F.coeff (Finsupp.single 1 1)) hlin
  have h0 : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 1 := by
    intro h
    have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
    simp at this
  have h1 : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro h
    have := congrArg (fun f : Fin 2 →₀ ℕ => f 1) h
    simp at this
  have h01 : (Finsupp.single 0 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro h
    have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
    simp at this
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_C_mul] at hx hy
  apply Prod.ext
  · simpa [MvPolynomial.coeff_X,
      MvPolynomial.coeff_C, h1, h01, sub_eq_zero] using hy
  · symm
    simpa [MvPolynomial.coeff_X,
      MvPolynomial.coeff_C, h0, Ne.symm h01, sub_eq_zero] using hx

/-- Evaluate z at the factor root and u at x−q₁ inside the plane's fraction field. -/
def evaluateRestriction (q : K × K) : Polynomial (Polynomial K) →+* PlaneFraction K :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (planeEmbed.comp MvPolynomial.C) (factorRoot q))
    (planeEmbed (MvPolynomial.X 0 - MvPolynomial.C q.1))

theorem evaluate_planeToUZ (q : K × K) (F : Plane K) :
    evaluateRestriction q (SlopeSubstitution.planeToUZ q F) = planeEmbed F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [evaluateRestriction, SlopeSubstitution.planeToUZ, Polynomial.algebraMap_eq]
  | add F G hF hG => simp only [map_add, hF, hG]
  | mul_X F i hF =>
    simp only [map_mul, hF]
    congr 1
    fin_cases i
    · simp [evaluateRestriction, SlopeSubstitution.planeToUZ]
    · have hn := denominator_ne_zero q
      rw [map_sub] at hn
      simp [evaluateRestriction, SlopeSubstitution.planeToUZ, factorRoot,
        div_mul_cancel₀ _ hn]

/-- The vanishing restriction gives an actual root of S in the plane's fraction field. -/
theorem evaluate_pointRestriction (q : K × K) (S : Polynomial (Plane K)) :
    evaluateRestriction q (SlopeSubstitution.pointRestriction q S) =
      S.eval₂ planeEmbed (factorRoot q) := by
  have hhom : (evaluateRestriction q).comp (SlopeSubstitution.pointRestriction q) =
      Polynomial.eval₂RingHom planeEmbed (factorRoot q) := by
    apply Polynomial.ringHom_ext
    · intro F
      simp only [RingHom.comp_apply, SlopeSubstitution.pointRestriction,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      exact evaluate_planeToUZ q F
    · simp [evaluateRestriction, SlopeSubstitution.pointRestriction]
  exact RingHom.congr_fun hhom S

def exceptionalSet (P : Finset (K × K)) (S : Polynomial (Plane K)) : Finset (K × K) :=
  P.filter (fun q => SlopeSubstitution.pointRestriction q S = 0)

theorem exceptionalSet_subset (P : Finset (K × K)) (S : Polynomial (Plane K)) :
    exceptionalSet P S ⊆ P := Finset.filter_subset _ _

theorem pointRestriction_ne_zero_of_mem_sdiff (P : Finset (K × K))
    (S : Polynomial (Plane K)) {q : K × K} (hq : q ∈ P \ exceptionalSet P S) :
    SlopeSubstitution.pointRestriction q S ≠ 0 := by
  intro hz
  exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hq).1, hz⟩)

theorem eval_factorRoot_eq_zero {q : K × K} {S : Polynomial (Plane K)}
    (hq : SlopeSubstitution.pointRestriction q S = 0) :
    (S.map planeEmbed).eval (factorRoot q) = 0 := by
  rw [Polynomial.eval_map, ← evaluate_pointRestriction, hq, map_zero]

/-- Exact exceptional bound, from nonzero S and its original z-degree alone. -/
theorem exceptionalSet_card_le (P : Finset (K × K)) (S : Polynomial (Plane K))
    (hS : S ≠ 0) {e : ℕ} (he : S.natDegree ≤ e) : (exceptionalSet P S).card ≤ e := by
  by_contra hnot
  have hmap : S.map planeEmbed ≠ 0 := by
    intro hz
    exact hS ((Polynomial.map_injective _ planeEmbed_injective) (hz.trans (Polynomial.map_zero _).symm))
  apply hmap
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (S.map planeEmbed)
    (f := fun q : exceptionalSet P S => factorRoot q)
    (factorRoot_injective.comp Subtype.val_injective)
  · intro q
    exact eval_factorRoot_eq_zero (Finset.mem_filter.mp q.property).2
  · have hdeg := (Polynomial.natDegree_map_le (p := S) (f := planeEmbed)).trans he
    simpa using (Nat.lt_of_le_of_lt hdeg (Nat.lt_of_not_ge hnot))

end MathCollab.Exceptional

#print axioms MathCollab.Exceptional.factorRoot_injective
#print axioms MathCollab.Exceptional.evaluate_pointRestriction
#print axioms MathCollab.Exceptional.exceptionalSet_card_le
