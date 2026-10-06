module
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

@[expose] public section

/-!
# Bounded-total-degree spaces of bivariate polynomials

Project-local conventions for the incidence formalization (Lewko, arXiv:2609.27023v2).

* The canonical bivariate ring is `MvPolynomial (Fin 2) K`; `X 0` is `X` and `X 1` is `Y`.
* `degSpace K M` is the `K`-subspace `Π_M` of polynomials of total degree at most `M`.
  It is Mathlib's `MvPolynomial.restrictTotalDegree`, which already carries a
  `Module.Finite` instance; this file only fixes notation and the membership interface.

No simp attributes are added here, to keep later polynomial conversions stable.
-/

namespace MathCollab

open MvPolynomial

variable (K : Type*) [Field K]

/-- `Π_M`: bivariate polynomials over `K` of total degree at most `M`. -/
noncomputable abbrev degSpace (M : ℕ) : Submodule K (MvPolynomial (Fin 2) K) :=
  MvPolynomial.restrictTotalDegree (Fin 2) K M

variable {K}

theorem mem_degSpace_iff {M : ℕ} {F : MvPolynomial (Fin 2) K} :
    F ∈ degSpace K M ↔ F.totalDegree ≤ M :=
  MvPolynomial.mem_restrictTotalDegree (Fin 2) M F

theorem degSpace_mono {M N : ℕ} (h : M ≤ N) : degSpace K M ≤ degSpace K N :=
  fun _ hF ↦ mem_degSpace_iff.mpr ((mem_degSpace_iff.mp hF).trans h)

example (M : ℕ) : Module.Finite K (degSpace K M) := inferInstance

/-- Exponent vectors of total degree at most `M`, as a disjoint union over exact degrees. -/
private theorem card_biUnion_finsuppAntidiag (M : ℕ) :
    ((Finset.range (M + 1)).biUnion fun k ↦
      (Finset.univ : Finset (Fin 2)).finsuppAntidiag k).card = (M + 2).choose 2 := by
  classical
  rw [Finset.card_biUnion]
  · simp only [Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Fintype.card_fin]
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, ih, show 2 + (M + 1) - 1 = (M + 1) + 1 by omega,
        Nat.choose_succ_self_right, show M + 1 + 2 = (M + 2) + 1 by omega,
        Nat.choose_succ_succ' (M + 2) 1, Nat.choose_one_right]
      simp only [Nat.reduceAdd]
      omega
  · intro a _ c _ hac
    refine Finset.disjoint_left.mpr fun n hna hnc ↦ hac ?_
    rw [Finset.mem_finsuppAntidiag] at hna hnc
    exact hna.1.symm.trans hnc.1

/-- `dim Π_M = (M + 2).choose 2`. -/
theorem finrank_degSpace (M : ℕ) : Module.finrank K (degSpace K M) = (M + 2).choose 2 := by
  classical
  have hS : {n : Fin 2 →₀ ℕ | (n.sum fun _ e ↦ e) ≤ M} =
      (((Finset.range (M + 1)).biUnion fun k ↦
        (Finset.univ : Finset (Fin 2)).finsuppAntidiag k : Finset (Fin 2 →₀ ℕ)) :
          Set (Fin 2 →₀ ℕ)) := by
    ext n
    simp [Finsupp.sum_fintype]
  have hb := Module.finrank_eq_nat_card_basis
    (MvPolynomial.basisRestrictSupport K {n : Fin 2 →₀ ℕ | (n.sum fun _ e ↦ e) ≤ M})
  refine hb.trans ?_
  rw [hS, Nat.card_coe_set_eq, Set.ncard_coe_finset, card_biUnion_finsuppAntidiag]

end MathCollab
