module
public import MathCollab.JetBudget
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-!
# Edge cases and kernel-dependency audit for contracts B and C

The `example`s instantiate the general theorems of `MathCollab.MulSpaces` and
`MathCollab.JetBudget`; they are checks on generality, not further proofs. Covered: empty
index type, zero heights, a nonzero constant polynomial, characteristic two, and the pair
`X, Y`, which shares no nonunit factor but is not `IsCoprime` (so the theorem genuinely
uses the divisor-theoretic hypothesis), where the budget `1 ≤ 1 * 1` is attained.
-/

namespace MathCollab

open MvPolynomial

/-- Empty family of lines. -/
example (K : Type*) [Field K] (ξ b : Empty → K) (h : Empty → ℕ)
    {F G : MvPolynomial (Fin 2) K} (hF0 : F ≠ 0) (hG0 : G ≠ 0) (hFG : IsRelPrime F G) :
    ∑ i, h i ≤ F.totalDegree * G.totalDegree :=
  sum_le_totalDegree_mul_of_jets ξ (b := b) (fun a ↦ a.elim) h hF0 hG0 hFG
    (fun i ↦ i.elim) (fun i ↦ i.elim)

/-- All heights zero: the divisibility hypotheses are vacuous (`u^0 = 1`). -/
example (K : Type*) [Field K] {J : Type*} [Fintype J] [DecidableEq J] (ξ : J → K)
    {b : J → K} (hb : Function.Injective b) {F G : MvPolynomial (Fin 2) K}
    (hF0 : F ≠ 0) (hG0 : G ≠ 0) (hFG : IsRelPrime F G) :
    ∑ _i : J, (0 : ℕ) ≤ F.totalDegree * G.totalDegree :=
  sum_le_totalDegree_mul_of_jets ξ hb (fun _ ↦ 0) hF0 hG0 hFG
    (fun _ ↦ by simp) (fun _ ↦ by simp)

/-- A nonzero constant `F = c` forces every height to vanish. -/
example (K : Type*) [Field K] {J : Type*} [Fintype J] [DecidableEq J] (ξ : J → K)
    {b : J → K} (hb : Function.Injective b) (h : J → ℕ) {c : K} (hc : c ≠ 0)
    {G : MvPolynomial (Fin 2) K} (hG0 : G ≠ 0)
    (hF : ∀ i, Polynomial.X ^ h i ∣ lineRestrict (ξ i) (b i) (C c))
    (hG : ∀ i, Polynomial.X ^ h i ∣ lineRestrict (ξ i) (b i) G) :
    ∑ i, h i = 0 := by
  have hu : IsUnit (C c : MvPolynomial (Fin 2) K) := (Ne.isUnit hc).map C
  have := sum_le_totalDegree_mul_of_jets ξ hb h (by simpa using hc) hG0 hu.isRelPrime_left hF hG
  simpa [totalDegree_C] using this

theorem X_zero_not_dvd_X_one (K : Type*) [Field K] :
    ¬ (X 0 : MvPolynomial (Fin 2) K) ∣ X 1 := by
  rintro ⟨q, hq⟩
  have := congrArg (eval ![(0 : K), 1]) hq
  simp at this

/-- `X` and `Y` share no nonunit factor. -/
theorem isRelPrime_X_zero_X_one (K : Type*) [Field K] :
    IsRelPrime (X 0 : MvPolynomial (Fin 2) K) (X 1) :=
  (X_prime (R := K) (i := (0 : Fin 2))).irreducible.isRelPrime_iff_not_dvd.mpr
    (X_zero_not_dvd_X_one K)

/-- ... but they are not `IsCoprime`: `A X + B Y = 1` fails at the origin. -/
theorem not_isCoprime_X_zero_X_one (K : Type*) [Field K] :
    ¬ IsCoprime (X 0 : MvPolynomial (Fin 2) K) (X 1) := by
  rintro ⟨A, B, hAB⟩
  have := congrArg (eval (0 : Fin 2 → K)) hAB
  simp at this

/-- The budget is attained by `F = X`, `G = Y` on the single line `Y = 0` at `ξ = 0`, `h = 1`:
both restrictions are divisible by `u`, and `1 ≤ deg X * deg Y = 1`. -/
example (K : Type*) [Field K] :
    ∑ _i : Unit, (1 : ℕ) ≤
      (X 0 : MvPolynomial (Fin 2) K).totalDegree * (X 1 : MvPolynomial (Fin 2) K).totalDegree := by
  refine sum_le_totalDegree_mul_of_jets (fun _ : Unit ↦ (0 : K)) (b := fun _ ↦ 0)
    (fun _ _ _ ↦ rfl) (fun _ ↦ 1) (X_ne_zero 0) (X_ne_zero 1) (isRelPrime_X_zero_X_one K)
    (fun _ ↦ ?_) (fun _ ↦ ?_)
  · simp [lineRestrict_X_zero]
  · simp [lineRestrict_X_one]

/-- Characteristic two: the theorem needs no characteristic hypothesis. -/
example (ξ : Fin 2 → ZMod 2) (h : Fin 2 → ℕ) {F G : MvPolynomial (Fin 2) (ZMod 2)}
    (hF0 : F ≠ 0) (hG0 : G ≠ 0) (hFG : IsRelPrime F G)
    (hF : ∀ i, Polynomial.X ^ h i ∣ lineRestrict (ξ i) (i.val : ZMod 2) F)
    (hG : ∀ i, Polynomial.X ^ h i ∣ lineRestrict (ξ i) (i.val : ZMod 2) G) :
    ∑ i, h i ≤ F.totalDegree * G.totalDegree :=
  sum_le_totalDegree_mul_of_jets ξ (b := fun i ↦ (i.val : ZMod 2)) (by decide) h hF0 hG0 hFG
    hF hG

#print axioms finrank_mulSpace
#print axioms mulSpace_inf_mulSpace
#print axioms choose_add_choose_add_mul
#print axioms finrank_mulSpace_sup_add_mul
#print axioms jetMap_mul_eq_zero
#print axioms mulSpace_le_jetKernel
#print axioms sum_le_totalDegree_mul_of_jets
#print axioms isRelPrime_X_zero_X_one
#print axioms not_isCoprime_X_zero_X_one

end MathCollab
