module
public import MathCollab.DegreeSpaces
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section

/-!
# Horizontal-line coefficient jets and their interpolation

Pilot module for Lewko, *A Szemerédi–Trotter theorem in arbitrary fields*
(arXiv:2609.27023v2). Fix a field `K`, a finite index type `J`, injective heights
`b : J → K`, base points `ξ : J → K`, and orders `h : J → ℕ`. Line `i` is `Y = b i`,
parametrised as `u ↦ (ξ i + u, b i)`.

* `lineRestrict ξ β : K[X,Y] →ₐ[K] K[u]` is `F ↦ F(ξ + u, β)`.
* `jetMap ξ b h F (i, j)` is the coefficient of `u^j` in `F(ξ i + u, b i)`, for `j < h i`.
* `jetMapDeg ξ b h M` is its restriction `Φ_M` to `Π_M`.
* `jetBasisPoly ξ b i j = (X - ξ i)^j * ∏_{v ≠ i} (Y - b v)/(b i - b v)`.
* `jetInterp ξ b h hM` is the explicit right inverse of `Φ_M` when `M ≥ |J| + ∑ h`.

Main results: `jetMapDeg_jetInterp`, `jetMapDeg_surjective`, and
`finrank_ker_jetMapDeg_add_sum`. These hold over every field (no characteristic
hypothesis) and allow `J` empty and any `h i = 0`. Jets are coefficient jets, not
derivatives divided by factorials, so `M` may exceed the characteristic.
-/

namespace MathCollab

open MvPolynomial
open scoped BigOperators

variable {K : Type*} [Field K]

/-! ### Restriction to a horizontal line -/

/-- Restriction to the horizontal line `Y = β`, translated by `ξ`: `F ↦ F(ξ + u, β)`. -/
noncomputable def lineRestrict (ξ β : K) : MvPolynomial (Fin 2) K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval ![Polynomial.C ξ + Polynomial.X, Polynomial.C β]

theorem lineRestrict_X_zero (ξ β : K) :
    lineRestrict ξ β (X 0) = Polynomial.C ξ + Polynomial.X := by
  simp [lineRestrict]

theorem lineRestrict_X_one (ξ β : K) : lineRestrict ξ β (X 1) = Polynomial.C β := by
  simp [lineRestrict]

theorem lineRestrict_C (ξ β a : K) : lineRestrict ξ β (C a) = Polynomial.C a := by
  simp [lineRestrict, Polynomial.algebraMap_eq]

/-! ### The jet map -/

/-- The coordinate index `Σ i : J, Fin (h i)`: pairs `(i, j)` with `j < h i`. -/
abbrev JetIndex {J : Type*} (h : J → ℕ) := Σ i : J, Fin (h i)

variable {J : Type*}

/-- The jet map on all bivariate polynomials:
`jetMap ξ b h F (i, j) = [u^j] F(ξ i + u, b i)`. -/
noncomputable def jetMap (ξ b : J → K) (h : J → ℕ) :
    MvPolynomial (Fin 2) K →ₗ[K] (JetIndex h → K) :=
  LinearMap.pi fun x ↦
    Polynomial.lcoeff K (x.2 : ℕ) ∘ₗ (lineRestrict (ξ x.1) (b x.1)).toLinearMap

theorem jetMap_apply (ξ b : J → K) (h : J → ℕ) (F : MvPolynomial (Fin 2) K)
    (x : JetIndex h) :
    jetMap ξ b h F x = (lineRestrict (ξ x.1) (b x.1) F).coeff x.2 :=
  rfl

/-- `Φ_M`: the jet map restricted to `Π_M`. -/
noncomputable def jetMapDeg (ξ b : J → K) (h : J → ℕ) (M : ℕ) :
    degSpace K M →ₗ[K] (JetIndex h → K) :=
  jetMap ξ b h ∘ₗ (degSpace K M).subtype

theorem jetMapDeg_apply (ξ b : J → K) (h : J → ℕ) (M : ℕ) (F : degSpace K M)
    (x : JetIndex h) :
    jetMapDeg ξ b h M F x = (lineRestrict (ξ x.1) (b x.1) (F : MvPolynomial (Fin 2) K)).coeff x.2 :=
  rfl

/-! ### The interpolating polynomials -/

variable [Fintype J] [DecidableEq J]

/-- The scalar `∏_{v ≠ i} (β - b v)/(b i - b v)`: the Lagrange factor of node `i` evaluated
at `β`. -/
noncomputable def lagrangeScalar (b : J → K) (i : J) (β : K) : K :=
  ∏ v ∈ Finset.univ.erase i, (b i - b v)⁻¹ * (β - b v)

theorem lagrangeScalar_self {b : J → K} (hb : Function.Injective b) (i : J) :
    lagrangeScalar b i (b i) = 1 := by
  refine Finset.prod_eq_one fun v hv ↦ ?_
  have hne : b i - b v ≠ 0 := sub_ne_zero.mpr fun h ↦ (Finset.ne_of_mem_erase hv) (hb h).symm
  exact inv_mul_cancel₀ hne

theorem lagrangeScalar_of_ne (b : J → K) {i w : J} (hw : w ≠ i) :
    lagrangeScalar b i (b w) = 0 :=
  Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hw, Finset.mem_univ w⟩) (by simp)

/-- The `Y`-factor `∏_{v ≠ i} (Y - b v)/(b i - b v)` as a bivariate polynomial. -/
noncomputable def lagrangeY (b : J → K) (i : J) : MvPolynomial (Fin 2) K :=
  ∏ v ∈ Finset.univ.erase i, C (b i - b v)⁻¹ * (X 1 - C (b v))

theorem lineRestrict_lagrangeY (ξ β : K) (b : J → K) (i : J) :
    lineRestrict ξ β (lagrangeY b i) = Polynomial.C (lagrangeScalar b i β) := by
  rw [lagrangeY, lagrangeScalar, map_prod, map_prod]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [map_mul, map_sub, lineRestrict_C, lineRestrict_C, lineRestrict_X_one, Polynomial.C_mul,
    Polynomial.C_sub]

theorem totalDegree_lagrangeY_le (b : J → K) (i : J) :
    (lagrangeY b i).totalDegree ≤ Fintype.card J - 1 := by
  refine (totalDegree_finsetProd _ _).trans ?_
  have hfac : ∀ v ∈ Finset.univ.erase i,
      (C (b i - b v)⁻¹ * (X 1 - C (b v)) : MvPolynomial (Fin 2) K).totalDegree ≤ 1 := by
    intro v _
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    refine (totalDegree_sub _ _).trans ?_
    rw [totalDegree_X, totalDegree_C]
    exact max_le le_rfl (Nat.zero_le 1)
  refine (Finset.sum_le_sum hfac).trans ?_
  simp [Finset.card_erase_of_mem]

/-- `B_{i,j}(X,Y) = (X - ξ i)^j * ∏_{v ≠ i} (Y - b v)/(b i - b v)`. -/
noncomputable def jetBasisPoly (ξ b : J → K) (i : J) (j : ℕ) : MvPolynomial (Fin 2) K :=
  (X 0 - C (ξ i)) ^ j * lagrangeY b i

theorem lineRestrict_jetBasisPoly (ξ b : J → K) (i : J) (j : ℕ) (ξ' β : K) :
    lineRestrict ξ' β (jetBasisPoly ξ b i j) =
      (Polynomial.C (ξ' - ξ i) + Polynomial.X) ^ j * Polynomial.C (lagrangeScalar b i β) := by
  rw [jetBasisPoly, map_mul, map_pow, map_sub, lineRestrict_X_zero, lineRestrict_C,
    lineRestrict_lagrangeY, Polynomial.C_sub]
  ring

/-- On its own line, `B_{i,j}` restricts to `u^j`. -/
theorem lineRestrict_jetBasisPoly_self (ξ : J → K) {b : J → K} (hb : Function.Injective b)
    (i : J) (j : ℕ) :
    lineRestrict (ξ i) (b i) (jetBasisPoly ξ b i j) = Polynomial.X ^ j := by
  rw [lineRestrict_jetBasisPoly, sub_self, lagrangeScalar_self hb, Polynomial.C_0,
    Polynomial.C_1, zero_add, mul_one]

/-- On every other indexed line, `B_{i,j}` restricts to `0`. -/
theorem lineRestrict_jetBasisPoly_of_ne (ξ b : J → K) {i w : J} (hw : w ≠ i) (j : ℕ) :
    lineRestrict (ξ w) (b w) (jetBasisPoly ξ b i j) = 0 := by
  rw [lineRestrict_jetBasisPoly, lagrangeScalar_of_ne b hw, Polynomial.C_0, mul_zero]

theorem totalDegree_jetBasisPoly_le (ξ b : J → K) (i : J) (j : ℕ) :
    (jetBasisPoly ξ b i j).totalDegree ≤ j + (Fintype.card J - 1) := by
  refine (totalDegree_mul _ _).trans (add_le_add ?_ (totalDegree_lagrangeY_le b i))
  refine (totalDegree_pow _ _).trans ?_
  have : (X 0 - C (ξ i) : MvPolynomial (Fin 2) K).totalDegree ≤ 1 := by
    refine (totalDegree_sub _ _).trans ?_
    rw [totalDegree_X, totalDegree_C]
    exact max_le le_rfl (Nat.zero_le 1)
  simpa using Nat.mul_le_mul_left j this

/-- The jet vector of `B_{i,j}` is the coordinate vector at `(i, j)`. -/
theorem jetMap_jetBasisPoly (ξ : J → K) {b : J → K} (hb : Function.Injective b)
    (h : J → ℕ) (x : JetIndex h) :
    jetMap ξ b h (jetBasisPoly ξ b x.1 x.2) = Pi.single x 1 := by
  funext y
  obtain ⟨i, j⟩ := x
  obtain ⟨w, j'⟩ := y
  rw [jetMap_apply]
  by_cases hw : w = i
  · subst hw
    rw [lineRestrict_jetBasisPoly_self ξ hb, Polynomial.coeff_X_pow, Pi.single_apply]
    simp [Fin.val_inj]
  · rw [lineRestrict_jetBasisPoly_of_ne ξ b hw, Polynomial.coeff_zero, Pi.single_apply]
    split_ifs with hxy
    · exact absurd (congrArg Sigma.fst hxy) hw
    · rfl

theorem jetBasisPoly_mem_degSpace (ξ b : J → K) {h : J → ℕ} {M : ℕ}
    (hM : Fintype.card J + ∑ i, h i ≤ M) (x : JetIndex h) :
    jetBasisPoly ξ b x.1 x.2 ∈ degSpace K M := by
  rw [mem_degSpace_iff]
  have hj : (x.2 : ℕ) < h x.1 := x.2.isLt
  have hle : h x.1 ≤ ∑ i, h i :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ x.1)
  have := totalDegree_jetBasisPoly_le ξ b x.1 x.2
  omega

/-! ### The explicit right inverse, surjectivity, and the kernel formula -/

/-- The explicit right inverse of `Φ_M`: prescribed jet values `c` go to `∑ c (i,j) • B_{i,j}`. -/
noncomputable def jetInterp (ξ b : J → K) (h : J → ℕ) {M : ℕ}
    (hM : Fintype.card J + ∑ i, h i ≤ M) : (JetIndex h → K) →ₗ[K] degSpace K M :=
  Fintype.linearCombination K fun x ↦ ⟨jetBasisPoly ξ b x.1 x.2, jetBasisPoly_mem_degSpace ξ b hM x⟩

theorem jetInterp_apply_coe (ξ b : J → K) (h : J → ℕ) {M : ℕ}
    (hM : Fintype.card J + ∑ i, h i ≤ M) (c : JetIndex h → K) :
    (jetInterp ξ b h hM c : MvPolynomial (Fin 2) K) = ∑ x, c x • jetBasisPoly ξ b x.1 x.2 := by
  simp [jetInterp, Fintype.linearCombination_apply]

/-- `Φ_M ∘ jetInterp = id`. -/
theorem jetMapDeg_comp_jetInterp (ξ : J → K) {b : J → K} (hb : Function.Injective b)
    (h : J → ℕ) {M : ℕ} (hM : Fintype.card J + ∑ i, h i ≤ M) :
    jetMapDeg ξ b h M ∘ₗ jetInterp ξ b h hM = LinearMap.id := by
  refine LinearMap.pi_ext fun x r ↦ ?_
  rw [LinearMap.comp_apply, jetInterp, Fintype.linearCombination_apply_single, map_smul,
    LinearMap.id_apply]
  change r • jetMap ξ b h (jetBasisPoly ξ b x.1 x.2) = _
  rw [jetMap_jetBasisPoly ξ hb, ← Pi.single_smul, smul_eq_mul, mul_one]

theorem jetMapDeg_jetInterp (ξ : J → K) {b : J → K} (hb : Function.Injective b)
    (h : J → ℕ) {M : ℕ} (hM : Fintype.card J + ∑ i, h i ≤ M) (c : JetIndex h → K) :
    jetMapDeg ξ b h M (jetInterp ξ b h hM c) = c :=
  LinearMap.congr_fun (jetMapDeg_comp_jetInterp ξ hb h hM) c

/-- **Pilot theorem, surjectivity.** If `M ≥ |J| + ∑ h`, then `Φ_M` is surjective. -/
theorem jetMapDeg_surjective (ξ : J → K) {b : J → K} (hb : Function.Injective b)
    (h : J → ℕ) {M : ℕ} (hM : Fintype.card J + ∑ i, h i ≤ M) :
    Function.Surjective (jetMapDeg ξ b h M) :=
  fun c ↦ ⟨jetInterp ξ b h hM c, jetMapDeg_jetInterp ξ hb h hM c⟩

/-- **Pilot theorem, kernel formula.** If `M ≥ |J| + ∑ h`, then
`dim ker Φ_M + ∑ h = dim Π_M`. -/
theorem finrank_ker_jetMapDeg_add_sum (ξ : J → K) {b : J → K} (hb : Function.Injective b)
    (h : J → ℕ) {M : ℕ} (hM : Fintype.card J + ∑ i, h i ≤ M) :
    Module.finrank K (LinearMap.ker (jetMapDeg ξ b h M)) + ∑ i, h i =
      Module.finrank K (degSpace K M) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (jetMapDeg ξ b h M)
  rw [LinearMap.range_eq_top.mpr (jetMapDeg_surjective ξ hb h hM), finrank_top,
    Module.finrank_fintype_fun_eq_card, Fintype.card_sigma] at hrn
  simp only [Fintype.card_fin] at hrn
  omega

/-- Closed form of the kernel formula: `dim ker Φ_M + ∑ h = (M + 2).choose 2`. -/
theorem finrank_ker_jetMapDeg_add_sum_eq_choose (ξ : J → K) {b : J → K}
    (hb : Function.Injective b) (h : J → ℕ) {M : ℕ} (hM : Fintype.card J + ∑ i, h i ≤ M) :
    Module.finrank K (LinearMap.ker (jetMapDeg ξ b h M)) + ∑ i, h i = (M + 2).choose 2 :=
  (finrank_ker_jetMapDeg_add_sum ξ hb h hM).trans (finrank_degSpace M)

end MathCollab
