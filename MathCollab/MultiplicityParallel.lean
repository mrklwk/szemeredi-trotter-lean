module
public import MathCollab.Multiplicity

@[expose] public section

/-!
# The multiplicity bound for arbitrary parallel lines

Extends `sum_sub_one_le_of_squarefree` (horizontal lines) to the full parallel-line form
of Lewko's Lemma 3.1, by the paper's two coordinate changes:

* nonvertical lines `y = a x + b i` through `(ξ i, a ξ i + b i)` with direction `(1, a)`:
  the shear `T(X, Y) = F(X, Y + a X)` sends them to the horizontal lines `Y = b i`;
* vertical lines `x = c i` through `(c i, η i)` with direction `(0, 1)`: the coordinate swap.

Both substitutions are `K`-algebra automorphisms given by linear forms, so they preserve
nonvanishing and squarefreeness and do not increase total degree.
-/

namespace MathCollab

open MvPolynomial

variable {K : Type*} [Field K]

/-! ### Linear substitutions and automorphisms -/

/-- Substituting polynomials of total degree `≤ 1` does not raise total degree. -/
theorem totalDegree_aeval_le_of_linear (g : Fin 2 → MvPolynomial (Fin 2) K)
    (hg : ∀ i, (g i).totalDegree ≤ 1) (F : MvPolynomial (Fin 2) K) :
    (aeval g F).totalDegree ≤ F.totalDegree := by
  conv_lhs => rw [F.as_sum, map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm ↦ ?_)
  rw [aeval_monomial, MvPolynomial.algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add, Finsupp.prod]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ ↦ (totalDegree_pow _ _).trans
    (Nat.mul_le_mul_left (m i) (hg i))).trans ?_
  simp only [mul_one]
  exact le_totalDegree hm

theorem Squarefree.map_algEquiv {A B : Type*} [CommRing A] [CommRing B] [Algebra K A]
    [Algebra K B] (e : A ≃ₐ[K] B) {F : A} (hF : Squarefree F) : Squarefree (e F) := by
  intro x hx
  have h : e.symm x * e.symm x ∣ F := by
    simpa using map_dvd e.symm.toAlgHom hx
  simpa using (hF _ h).map e

/-! ### The shear `(X, Y) ↦ (X, Y + a X)` -/

/-- `shear a F = F(X, Y + a X)`. -/
noncomputable def shear (a : K) : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K :=
  aeval ![X 0, X 1 + C a * X 0]

theorem shear_comp_shear_neg (a : K) : (shear a).comp (shear (-a)) = AlgHom.id K _ := by
  refine algHom_ext fun i ↦ ?_
  fin_cases i <;> simp [shear]

/-- The shear as an algebra automorphism. -/
noncomputable def shearEquiv (a : K) : MvPolynomial (Fin 2) K ≃ₐ[K] MvPolynomial (Fin 2) K :=
  AlgEquiv.ofAlgHom (shear a) (shear (-a)) (shear_comp_shear_neg a)
    (by simpa using shear_comp_shear_neg (-a))

theorem totalDegree_shear_le (a : K) (F : MvPolynomial (Fin 2) K) :
    (shear a F).totalDegree ≤ F.totalDegree := by
  refine totalDegree_aeval_le_of_linear _ (fun i ↦ ?_) F
  fin_cases i
  · simp [totalDegree_X]
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    refine (totalDegree_add _ _).trans (max_le (by simp [totalDegree_X]) ?_)
    refine (totalDegree_mul _ _).trans ?_
    simp [totalDegree_X]

/-- Restriction of `F` to the nonvertical line `y = a x + b` from `(ξ, a ξ + b)` in direction
`(1, a)`: `u ↦ F(ξ + u, a ξ + b + a u)`. -/
noncomputable def slopeRestrict (a ξ b : K) : MvPolynomial (Fin 2) K →ₐ[K] Polynomial K :=
  aeval ![Polynomial.C ξ + Polynomial.X, Polynomial.C (a * ξ + b) + Polynomial.C a * Polynomial.X]

theorem lineRestrict_shear (a ξ b : K) (F : MvPolynomial (Fin 2) K) :
    lineRestrict ξ b (shear a F) = slopeRestrict a ξ b F := by
  rw [← AlgHom.comp_apply]
  congr 1
  refine algHom_ext fun i ↦ ?_
  fin_cases i
  · simp [shear, slopeRestrict, lineRestrict_X_zero]
  · simp only [shear, slopeRestrict, AlgHom.comp_apply, aeval_X]
    simp [lineRestrict_X_zero, lineRestrict_X_one, Polynomial.C_add,
      Polynomial.C_mul]
    ring

/-! ### The coordinate swap -/

/-- Restriction of `F` to the vertical line `x = c` from `(c, η)` in direction `(0, 1)`:
`u ↦ F(c, η + u)`. -/
noncomputable def vertRestrict (c η : K) : MvPolynomial (Fin 2) K →ₐ[K] Polynomial K :=
  aeval ![Polynomial.C c, Polynomial.C η + Polynomial.X]

theorem lineRestrict_rename_swap (c η : K) (F : MvPolynomial (Fin 2) K) :
    lineRestrict η c (rename (Equiv.swap (0 : Fin 2) 1) F) = vertRestrict c η F := by
  rw [lineRestrict, aeval_rename, vertRestrict]
  congr 2
  funext i
  fin_cases i <;> simp

/-! ### Parallel-line multiplicity bounds -/

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- **Multiplicity bound, nonvertical parallel lines.** Lines `y = a x + b i` with distinct
intercepts, points `(ξ i, a ξ i + b i)`; characteristic `0` or `d < char K`; `F ≠ 0`
squarefree of total degree `≤ d` and not identically zero on any line; `u^(ν i)` divides the
restriction along direction `(1, a)`. Then `∑ (ν i - 1) ≤ d (d - 1)`. -/
theorem sum_sub_one_le_of_squarefree_slope (a : K) (ξ : J → K) {b : J → K}
    (hb : Function.Injective b) {d : ℕ} (hchar : ringChar K = 0 ∨ d < ringChar K)
    {F : MvPolynomial (Fin 2) K} (hF0 : F ≠ 0) (hsq : Squarefree F) (hdeg : F.totalDegree ≤ d)
    (ν : J → ℕ) (hres : ∀ i, slopeRestrict a (ξ i) (b i) F ≠ 0)
    (hdiv : ∀ i, Polynomial.X ^ ν i ∣ slopeRestrict a (ξ i) (b i) F) :
    ∑ i, (ν i - 1) ≤ d * (d - 1) := by
  have hT0 : shear a F ≠ 0 := by
    intro h
    exact hF0 ((shearEquiv a).injective (h.trans (map_zero (shearEquiv a)).symm))
  refine sum_sub_one_le_of_squarefree ξ hb hchar hT0 (Squarefree.map_algEquiv (shearEquiv a) hsq)
    ((totalDegree_shear_le a F).trans hdeg) ν (fun i ↦ ?_) (fun i ↦ ?_)
  · rw [lineRestrict_shear]; exact hres i
  · rw [lineRestrict_shear]; exact hdiv i

/-- **Multiplicity bound, vertical parallel lines.** Lines `x = c i` with distinct `c i`,
points `(c i, η i)`, direction `(0, 1)`; hypotheses as in the nonvertical case. -/
theorem sum_sub_one_le_of_squarefree_vertical (c : J → K) (hc : Function.Injective c)
    (η : J → K) {d : ℕ} (hchar : ringChar K = 0 ∨ d < ringChar K)
    {F : MvPolynomial (Fin 2) K} (hF0 : F ≠ 0) (hsq : Squarefree F) (hdeg : F.totalDegree ≤ d)
    (ν : J → ℕ) (hres : ∀ i, vertRestrict (c i) (η i) F ≠ 0)
    (hdiv : ∀ i, Polynomial.X ^ ν i ∣ vertRestrict (c i) (η i) F) :
    ∑ i, (ν i - 1) ≤ d * (d - 1) := by
  set e := renameEquiv K (Equiv.swap (0 : Fin 2) 1)
  have he : ∀ P, e P = rename (Equiv.swap (0 : Fin 2) 1) P := fun _ ↦ rfl
  have hT0 : e F ≠ 0 := by
    intro h; exact hF0 (e.injective (h.trans (map_zero e).symm))
  refine sum_sub_one_le_of_squarefree η hc hchar hT0 (Squarefree.map_algEquiv e hsq)
    ((he F ▸ totalDegree_rename_le _ F).trans hdeg) ν (fun i ↦ ?_) (fun i ↦ ?_)
  · rw [he, lineRestrict_rename_swap]; exact hres i
  · rw [he, lineRestrict_rename_swap]; exact hdiv i

end MathCollab
