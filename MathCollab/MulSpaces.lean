module
public import MathCollab.DegreeSpaces
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

@[expose] public section

/-!
# Bounded multiplication spaces and their intersection

Contract B of `EXACT_CONTRACTS.md` (Lewko, arXiv:2609.27023v2, proof of Lemma 3.1).
For a bivariate polynomial `F` and `N : ℕ`, `mulSpace F N = F · Π_N` is the image of
`Π_N` under multiplication by `F`.

For nonzero `F, G` with no common nonunit divisor (`IsRelPrime F G`, which unfolds to
`∀ D, D ∣ F → D ∣ G → IsUnit D`; this is NOT the Bézout condition `IsCoprime`), with
`r = deg F`, `t = deg G` and `M ≥ r + t`:

* `mulSpace_le_degSpace`: `F · Π_(M-r) ⊆ Π_M`;
* `finrank_mulSpace`: multiplication by `F ≠ 0` is injective, so `dim F · Π_N = dim Π_N`;
* `mulSpace_inf_mulSpace`: `F · Π_(M-r) ⊓ G · Π_(M-t) = FG · Π_(M-r-t)`;
* `finrank_mulSpace_sup_add_mul`: `dim (F · Π_(M-r) ⊔ G · Π_(M-t)) + r * t = dim Π_M`.

No characteristic or cardinality hypothesis on `K` is used.
-/

namespace MathCollab

open MvPolynomial

variable {K : Type*} [Field K]

/-- `F · Π_N`: the products `F * U` with `U` of total degree at most `N`. -/
noncomputable def mulSpace (F : MvPolynomial (Fin 2) K) (N : ℕ) :
    Submodule K (MvPolynomial (Fin 2) K) :=
  (degSpace K N).map (LinearMap.mulLeft K F)

theorem mem_mulSpace_iff {F H : MvPolynomial (Fin 2) K} {N : ℕ} :
    H ∈ mulSpace F N ↔ ∃ U, U.totalDegree ≤ N ∧ F * U = H := by
  simp only [mulSpace, Submodule.mem_map, mem_degSpace_iff, LinearMap.mulLeft_apply]

theorem mul_mem_mulSpace (F : MvPolynomial (Fin 2) K) {U : MvPolynomial (Fin 2) K} {N : ℕ}
    (hU : U.totalDegree ≤ N) : F * U ∈ mulSpace F N :=
  mem_mulSpace_iff.mpr ⟨U, hU, rfl⟩

/-- `F · Π_(M - deg F) ⊆ Π_M` whenever `deg F ≤ M`. -/
theorem mulSpace_le_degSpace (F : MvPolynomial (Fin 2) K) {M : ℕ} (hM : F.totalDegree ≤ M) :
    mulSpace F (M - F.totalDegree) ≤ degSpace K M := by
  intro H hH
  obtain ⟨U, hU, rfl⟩ := mem_mulSpace_iff.mp hH
  rw [mem_degSpace_iff]
  have := totalDegree_mul F U
  omega

theorem mulLeft_injective {F : MvPolynomial (Fin 2) K} (hF : F ≠ 0) :
    Function.Injective (LinearMap.mulLeft K F) :=
  mul_right_injective₀ hF

instance (F : MvPolynomial (Fin 2) K) (N : ℕ) : FiniteDimensional K (mulSpace F N) := by
  unfold mulSpace; infer_instance

/-- Multiplication by a nonzero polynomial is injective, so `dim F · Π_N = dim Π_N`. -/
theorem finrank_mulSpace {F : MvPolynomial (Fin 2) K} (hF : F ≠ 0) (N : ℕ) :
    Module.finrank K (mulSpace F N) = (N + 2).choose 2 := by
  rw [mulSpace, ← LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective _ (mulLeft_injective hF) (degSpace K N)), finrank_degSpace]

/-- The relative-primality intersection: for nonzero `F, G` sharing no nonunit factor and
`deg F + deg G ≤ M`, `F · Π_(M-r) ⊓ G · Π_(M-t) = FG · Π_(M-r-t)`. -/
theorem mulSpace_inf_mulSpace {F G : MvPolynomial (Fin 2) K} (hF : F ≠ 0) (hG : G ≠ 0)
    (hFG : IsRelPrime F G) {M : ℕ} (hM : F.totalDegree + G.totalDegree ≤ M) :
    mulSpace F (M - F.totalDegree) ⊓ mulSpace G (M - G.totalDegree) =
      mulSpace (F * G) (M - F.totalDegree - G.totalDegree) := by
  apply le_antisymm
  · rintro H ⟨hHF, hHG⟩
    obtain ⟨U, hU, rfl⟩ := mem_mulSpace_iff.mp hHF
    obtain ⟨V, -, hV⟩ := mem_mulSpace_iff.mp hHG
    obtain ⟨W, hW⟩ : F * G ∣ F * U :=
      hFG.mul_dvd (dvd_mul_right F U) (hV ▸ dvd_mul_right G V)
    refine mem_mulSpace_iff.mpr ⟨W, ?_, hW.symm⟩
    by_cases hW0 : W = 0
    · rw [hW0, totalDegree_zero]; exact Nat.zero_le _
    · -- `F * U = F * G * W` with `W ≠ 0`, so `U = G * W` and `deg U = deg G + deg W`.
      have hUGW : U = G * W := mul_left_cancel₀ hF (by rw [hW, mul_assoc])
      have hdeg : U.totalDegree = G.totalDegree + W.totalDegree := by
        rw [hUGW, totalDegree_mul_of_isDomain hG hW0]
      omega
  · intro H hH
    obtain ⟨W, hW, rfl⟩ := mem_mulSpace_iff.mp hH
    refine ⟨?_, ?_⟩
    · rw [mul_assoc]
      refine mul_mem_mulSpace F ((totalDegree_mul G W).trans ?_)
      omega
    · rw [mul_comm F G, mul_assoc]
      refine mul_mem_mulSpace G ((totalDegree_mul F W).trans ?_)
      omega

/-- `2 * choose (n + 2) 2 = (n + 2) * (n + 1)`. -/
theorem two_mul_choose_add_two (n : ℕ) : 2 * (n + 2).choose 2 = (n + 2) * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by omega, Nat.choose_succ_succ' (n + 2) 1,
      Nat.choose_one_right]
    simp only [Nat.reduceAdd] at ih ⊢
    nlinarith [ih]

/-- The binomial identity of the paper in additive form: for `r + t ≤ M`,
`C(M-r+2,2) + C(M-t+2,2) + r t = C(M+2,2) + C(M-r-t+2,2)`. -/
theorem choose_add_choose_add_mul {r t M : ℕ} (h : r + t ≤ M) :
    (M - r + 2).choose 2 + (M - t + 2).choose 2 + r * t =
      (M + 2).choose 2 + (M - r - t + 2).choose 2 := by
  obtain ⟨a, rfl⟩ : ∃ a, M = r + t + a := ⟨M - (r + t), by omega⟩
  rw [show r + t + a - r - t = a by omega, show r + t + a - r = t + a by omega,
    show r + t + a - t = r + a by omega]
  apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
  simp only [mul_add, two_mul_choose_add_two]
  ring

/-- Exact codimension: `dim (F · Π_(M-r) ⊔ G · Π_(M-t)) + r * t = dim Π_M`. -/
theorem finrank_mulSpace_sup_add_mul {F G : MvPolynomial (Fin 2) K} (hF : F ≠ 0)
    (hG : G ≠ 0) (hFG : IsRelPrime F G) {M : ℕ} (hM : F.totalDegree + G.totalDegree ≤ M) :
    Module.finrank K (mulSpace F (M - F.totalDegree) ⊔ mulSpace G (M - G.totalDegree) :
        Submodule K (MvPolynomial (Fin 2) K)) + F.totalDegree * G.totalDegree =
      Module.finrank K (degSpace K M) := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (mulSpace F (M - F.totalDegree)) (mulSpace G (M - G.totalDegree))
  rw [mulSpace_inf_mulSpace hF hG hFG hM, finrank_mulSpace (mul_ne_zero hF hG),
    finrank_mulSpace hF, finrank_mulSpace hG] at hdim
  have hbin := choose_add_choose_add_mul hM
  rw [finrank_degSpace]
  omega

end MathCollab
