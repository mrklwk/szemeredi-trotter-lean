module
public import MathCollab.Jets
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Rat.Cast.CharZero

@[expose] public section

/-!
# Edge-case instantiations and kernel-dependency audit for the jet-interpolation pilot

These `example`s only instantiate the general theorems of `MathCollab.Jets`; they are
checks on the statement's generality, not additional proofs. Covered: empty index type,
all heights zero, one line of arbitrary height, characteristic two, and a jet cutoff
larger than the characteristic.
-/

namespace MathCollab

/-- Empty family of lines: `Φ_M` has no coordinates and its kernel is all of `Π_M`. -/
example (K : Type*) [Field K] (ξ b : Empty → K) (h : Empty → ℕ) (M : ℕ) :
    Module.finrank K (LinearMap.ker (jetMapDeg ξ b h M)) = (M + 2).choose 2 := by
  have := finrank_ker_jetMapDeg_add_sum_eq_choose ξ (b := b) (fun a ↦ a.elim) h
    (M := M) (by simp)
  simpa using this

/-- All heights zero, three lines over `ℚ`. -/
example (ξ : Fin 3 → ℚ) (M : ℕ) (hM : 3 ≤ M) :
    Module.finrank ℚ (LinearMap.ker (jetMapDeg ξ (fun i ↦ (i.val : ℚ)) (fun _ ↦ 0) M)) =
      (M + 2).choose 2 := by
  have hb : Function.Injective fun i : Fin 3 ↦ (i.val : ℚ) :=
    Nat.cast_injective.comp Fin.val_injective
  have := finrank_ker_jetMapDeg_add_sum_eq_choose ξ hb (fun _ ↦ 0) (M := M) (by simpa using hM)
  simpa using this

/-- One line of arbitrary height `n`, over an arbitrary field. -/
example (K : Type*) [Field K] (ξ₀ b₀ : K) (n M : ℕ) (hM : 1 + n ≤ M) :
    Function.Surjective (jetMapDeg (fun _ : Unit ↦ ξ₀) (fun _ ↦ b₀) (fun _ ↦ n) M) ∧
      Module.finrank K
          (LinearMap.ker (jetMapDeg (fun _ : Unit ↦ ξ₀) (fun _ ↦ b₀) (fun _ ↦ n) M)) + n =
        (M + 2).choose 2 := by
  have hb : Function.Injective fun _ : Unit ↦ b₀ := fun _ _ _ ↦ rfl
  have hM' : Fintype.card Unit + ∑ _ : Unit, n ≤ M := by simpa using hM
  refine ⟨jetMapDeg_surjective _ hb _ hM', ?_⟩
  simpa using finrank_ker_jetMapDeg_add_sum_eq_choose (fun _ : Unit ↦ ξ₀) hb (fun _ ↦ n) hM'

/-- Characteristic two, with jet order `5` and cutoff `M = 12`, both exceeding `p = 2`. -/
example (ξ : Fin 2 → ZMod 2) :
    Function.Surjective (jetMapDeg ξ (fun i ↦ (i.val : ZMod 2)) (fun _ ↦ 5) 12) ∧
      Module.finrank (ZMod 2)
          (LinearMap.ker (jetMapDeg ξ (fun i ↦ (i.val : ZMod 2)) (fun _ ↦ 5) 12)) + 10 =
        91 := by
  have hb : Function.Injective fun i : Fin 2 ↦ (i.val : ZMod 2) := by decide
  have hM : Fintype.card (Fin 2) + ∑ _ : Fin 2, 5 ≤ 12 := by simp
  refine ⟨jetMapDeg_surjective ξ hb _ hM, ?_⟩
  simpa [Nat.choose_two_right] using finrank_ker_jetMapDeg_add_sum_eq_choose ξ hb (fun _ ↦ 5) hM

#print axioms finrank_degSpace
#print axioms jetMap_jetBasisPoly
#print axioms jetMapDeg_jetInterp
#print axioms jetMapDeg_surjective
#print axioms finrank_ker_jetMapDeg_add_sum
#print axioms finrank_ker_jetMapDeg_add_sum_eq_choose

end MathCollab
