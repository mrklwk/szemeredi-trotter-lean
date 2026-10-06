module
public import MathCollab.Jets
public import MathCollab.MulSpaces

@[expose] public section

/-!
# The generic horizontal-line jet budget

Contract C of `EXACT_CONTRACTS.md` (Lewko, arXiv:2609.27023v2, proof of Lemma 3.1).
Over any field `K`, for a finite family of distinct horizontal lines `Y = b i` with base
points `ξ i` and orders `h i`, and nonzero `F, G` sharing no nonunit factor
(`IsRelPrime F G`, not the Bézout condition `IsCoprime`), if `u^(h i)` divides both
`F(ξ i + u, b i)` and `G(ξ i + u, b i)` for every `i`, then
`∑ i, h i ≤ deg F * deg G`.

Proof: with `M = r + t + |J| + ∑ h`, the jet kernel `W_M ⊆ Π_M` has codimension `∑ h`
(`finrank_ker_jetMapDeg_add_sum`), contains `F · Π_(M-r) ⊔ G · Π_(M-t)`, and that sum
has codimension `r t` (`finrank_mulSpace_sup_add_mul`).

No characteristic hypothesis is used. `J` may be empty and any `h i` may be zero.
-/

namespace MathCollab

open MvPolynomial

variable {K : Type*} [Field K] {J : Type*}

/-- If `u^(h i)` divides `F(ξ i + u, b i)` for every `i`, every multiple of `F` has zero
jet vector. -/
theorem jetMap_mul_eq_zero (ξ b : J → K) (h : J → ℕ) {F : MvPolynomial (Fin 2) K}
    (hF : ∀ i, Polynomial.X ^ h i ∣ lineRestrict (ξ i) (b i) F) (U : MvPolynomial (Fin 2) K) :
    jetMap ξ b h (F * U) = 0 := by
  funext x
  obtain ⟨q, hq⟩ := hF x.1
  rw [jetMap_apply, map_mul, hq, mul_assoc, Polynomial.coeff_X_pow_mul']
  simp [Nat.not_le.mpr x.2.isLt]

/-- The jet kernel `W_M`, viewed as a subspace of the ambient polynomial ring. -/
noncomputable def jetKernel (ξ b : J → K) (h : J → ℕ) (M : ℕ) :
    Submodule K (MvPolynomial (Fin 2) K) :=
  (LinearMap.ker (jetMapDeg ξ b h M)).map (degSpace K M).subtype

theorem mem_jetKernel_iff (ξ b : J → K) (h : J → ℕ) (M : ℕ) {H : MvPolynomial (Fin 2) K} :
    H ∈ jetKernel ξ b h M ↔ H ∈ degSpace K M ∧ jetMap ξ b h H = 0 := by
  constructor
  · rintro ⟨H', hH', rfl⟩
    exact ⟨H'.2, hH'⟩
  · rintro ⟨hdeg, hjet⟩
    exact ⟨⟨H, hdeg⟩, hjet, rfl⟩

theorem finrank_jetKernel (ξ b : J → K) (h : J → ℕ) (M : ℕ) :
    Module.finrank K (jetKernel ξ b h M) = Module.finrank K (LinearMap.ker (jetMapDeg ξ b h M)) :=
  Submodule.finrank_map_subtype_eq _ _

instance (ξ b : J → K) (h : J → ℕ) (M : ℕ) : FiniteDimensional K (jetKernel ξ b h M) := by
  unfold jetKernel; infer_instance

/-- Every multiple of `F` of degree at most `M` lies in the jet kernel. -/
theorem mulSpace_le_jetKernel (ξ b : J → K) (h : J → ℕ) {F : MvPolynomial (Fin 2) K}
    (hF : ∀ i, Polynomial.X ^ h i ∣ lineRestrict (ξ i) (b i) F) {M : ℕ}
    (hM : F.totalDegree ≤ M) :
    mulSpace F (M - F.totalDegree) ≤ jetKernel ξ b h M := by
  intro H hH
  refine (mem_jetKernel_iff ξ b h M).mpr ⟨mulSpace_le_degSpace F hM hH, ?_⟩
  obtain ⟨U, -, rfl⟩ := mem_mulSpace_iff.mp hH
  exact jetMap_mul_eq_zero ξ b h hF U

variable [Fintype J] [DecidableEq J]

/-- **Generic jet budget (contract C).** Over any field, for distinct horizontal lines
`Y = b i`, base points `ξ i`, orders `h i`, and nonzero `F, G` with no common nonunit
factor, if `u^(h i)` divides `F(ξ i + u, b i)` and `G(ξ i + u, b i)` for all `i`, then
`∑ i, h i ≤ deg F * deg G`. -/
theorem sum_le_totalDegree_mul_of_jets (ξ : J → K) {b : J → K} (hb : Function.Injective b)
    (h : J → ℕ) {F G : MvPolynomial (Fin 2) K} (hF0 : F ≠ 0) (hG0 : G ≠ 0)
    (hFG : IsRelPrime F G)
    (hF : ∀ i, Polynomial.X ^ h i ∣ lineRestrict (ξ i) (b i) F)
    (hG : ∀ i, Polynomial.X ^ h i ∣ lineRestrict (ξ i) (b i) G) :
    ∑ i, h i ≤ F.totalDegree * G.totalDegree := by
  set M := F.totalDegree + G.totalDegree + (Fintype.card J + ∑ i, h i) with hMdef
  have hM1 : F.totalDegree + G.totalDegree ≤ M := by omega
  have hM2 : Fintype.card J + ∑ i, h i ≤ M := by omega
  have hker := finrank_ker_jetMapDeg_add_sum ξ hb h hM2
  have hsup := finrank_mulSpace_sup_add_mul hF0 hG0 hFG hM1
  have hle := Submodule.finrank_mono (sup_le
    (mulSpace_le_jetKernel ξ b h hF (by omega : F.totalDegree ≤ M))
    (mulSpace_le_jetKernel ξ b h hG (by omega : G.totalDegree ≤ M)))
  rw [finrank_jetKernel] at hle
  omega

end MathCollab
