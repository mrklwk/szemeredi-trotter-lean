module
public import MathCollab.MultiplicityParallel
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.CharP.Lemmas

@[expose] public section

/-!
# Edge cases and kernel-dependency audit for contract D (multiplicity)

The `example`s instantiate the general theorems of `MathCollab.Multiplicity` and
`MathCollab.MultiplicityParallel`; they check generality, not further mathematics.
Covered: empty index type, the constant polynomial `1` with `d = 0`, characteristic two
with `d = 1 < 2`, characteristic zero, and the nonvertical and vertical parallel forms.
The strict hypothesis `d < char K` is a visible parameter of every positive-characteristic
statement.
-/

namespace MathCollab

open MvPolynomial

/-- Empty family of lines. -/
example (K : Type*) [Field K] (ξ b : Empty → K) {d : ℕ}
    (hchar : ringChar K = 0 ∨ d < ringChar K) {T : MvPolynomial (Fin 2) K} (hT0 : T ≠ 0)
    (hsq : Squarefree T) (hdeg : T.totalDegree ≤ d) (ν : Empty → ℕ) :
    ∑ i, (ν i - 1) ≤ d * (d - 1) :=
  sum_sub_one_le_of_squarefree ξ (b := b) (fun a ↦ a.elim) hchar hT0 hsq hdeg ν
    (fun i ↦ i.elim) (fun i ↦ i.elim)

/-- The constant `1` (degree `0`, any characteristic since `0 < char` or `char = 0`). -/
example (K : Type*) [Field K] {J : Type*} [Fintype J] [DecidableEq J] (ξ : J → K)
    {b : J → K} (hb : Function.Injective b) (ν : J → ℕ)
    (hdiv : ∀ i, Polynomial.X ^ ν i ∣ lineRestrict (ξ i) (b i) (1 : MvPolynomial (Fin 2) K)) :
    ∑ i, (ν i - 1) = 0 := by
  have hchar : ringChar K = 0 ∨ 0 < ringChar K := by omega
  have := sum_sub_one_le_of_squarefree ξ hb hchar one_ne_zero squarefree_one
    (by simp) ν (fun i ↦ by simp) hdiv
  simpa using this

/-- Characteristic two, `T = X`, `d = 1 < 2`: every multiplicity is at most `1`. -/
example (ξ : Fin 2 → ZMod 2) (ν : Fin 2 → ℕ)
    (hdiv : ∀ i, Polynomial.X ^ ν i ∣
      lineRestrict (ξ i) (i.val : ZMod 2) (X 0 : MvPolynomial (Fin 2) (ZMod 2))) :
    ∑ i, (ν i - 1) = 0 := by
  have hX : (X 0 : MvPolynomial (Fin 2) (ZMod 2)).totalDegree ≤ 1 := by simp [totalDegree_X]
  have := sum_sub_one_le_of_squarefree_charP 2 ξ (b := fun i ↦ (i.val : ZMod 2)) (by decide)
    (by norm_num : 1 < 2) (X_ne_zero 0) (X_prime.irreducible.squarefree) hX ν
    (fun i ↦ by
      rw [lineRestrict_X_zero, add_comm]
      exact Polynomial.X_add_C_ne_zero _)
    hdiv
  simpa using this

/-- Characteristic zero, no bound on `d`. -/
example (ξ : Fin 3 → ℚ) {T : MvPolynomial (Fin 2) ℚ} (hT0 : T ≠ 0) (hsq : Squarefree T)
    (ν : Fin 3 → ℕ) (hres : ∀ i, lineRestrict (ξ i) (i.val : ℚ) T ≠ 0)
    (hdiv : ∀ i, Polynomial.X ^ ν i ∣ lineRestrict (ξ i) (i.val : ℚ) T) :
    ∑ i, (ν i - 1) ≤ T.totalDegree * (T.totalDegree - 1) :=
  sum_sub_one_le_of_squarefree_charZero ξ (b := fun i ↦ (i.val : ℚ))
    (Nat.cast_injective.comp Fin.val_injective) hT0 hsq le_rfl ν hres hdiv

#print axioms lineRestrict_pderiv_zero
#print axioms exists_yOnly_mul
#print axioms pderiv_zero_ne_zero
#print axioms isRelPrime_pderiv_zero
#print axioms sum_sub_one_le_of_squarefree
#print axioms sum_sub_one_le_of_squarefree_charZero
#print axioms sum_sub_one_le_of_squarefree_charP
#print axioms totalDegree_aeval_le_of_linear
#print axioms lineRestrict_shear
#print axioms lineRestrict_rename_swap
#print axioms sum_sub_one_le_of_squarefree_slope
#print axioms sum_sub_one_le_of_squarefree_vertical

end MathCollab
