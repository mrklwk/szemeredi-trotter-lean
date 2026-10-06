module
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Finset.Prod

/-! Statement-only specification for Comparator checking.
The four deliberate holes are NOT proofs and are not imported by Solution.
The complete proofs are in Solution and MathCollab. See verification/ for checks.
The incidence set is the ordinary filtered product of points and affine lines.
Only the prime_field theorem restricts the field to the prime field ZMod p. -/

@[expose] public section

noncomputable section
open Classical
open scoped BigOperators

namespace IncidenceBounds

theorem arbitrary_charZero {K : Type*} [Field K] [CharZero K]
    (P : Finset (K × K)) (L : Finset (AffineSubspace K (K × K)))
    (hL : ∀ l ∈ L, Module.finrank K l.direction = 1) :
    (((P ×ˢ L).filter (fun z => z.1 ∈ z.2)).card : ℝ) ≤
      3 * ((P.card : ℝ) * (L.card : ℝ)) ^ ((2 : ℝ) / 3) +
        (P.card : ℝ) + (L.card : ℝ) := by
  sorry

theorem arbitrary_charP {K : Type*} [Field K] (p : ℕ) [CharP K p] (hp : p ≠ 0)
    (P : Finset (K × K)) (L : Finset (AffineSubspace K (K × K)))
    (hL : ∀ l ∈ L, Module.finrank K l.direction = 1) :
    (((P ×ˢ L).filter (fun z => z.1 ∈ z.2)).card : ℝ) ≤
      3 * ((P.card : ℝ) * (L.card : ℝ)) ^ ((2 : ℝ) / 3) +
        (P.card : ℝ) + (L.card : ℝ) +
        2 * (P.card : ℝ) * (L.card : ℝ) / (p : ℝ) := by
  sorry

theorem subcritical {K : Type*} [Field K] (p : ℕ) [CharP K p] (hp : p ≠ 0)
    (P : Finset (K × K)) (L : Finset (AffineSubspace K (K × K)))
    (hL : ∀ l ∈ L, Module.finrank K l.direction = 1)
    (hcap : P.card * L.card ≤ p ^ 3) :
    (((P ×ˢ L).filter (fun z => z.1 ∈ z.2)).card : ℝ) ≤
      3 * ((P.card : ℝ) * (L.card : ℝ)) ^ ((2 : ℝ) / 3) +
        (P.card : ℝ) + (L.card : ℝ) := by
  sorry

theorem prime_field (p : ℕ) [Fact (Nat.Prime p)]
    (P : Finset (ZMod p × ZMod p))
    (L : Finset (AffineSubspace (ZMod p) (ZMod p × ZMod p)))
    (hL : ∀ l ∈ L, Module.finrank (ZMod p) l.direction = 1) :
    (((P ×ˢ L).filter (fun z => z.1 ∈ z.2)).card : ℝ) ≤
      3 * ((P.card : ℝ) * (L.card : ℝ)) ^ ((2 : ℝ) / 3) +
        (P.card : ℝ) + (L.card : ℝ) + (P.card : ℝ) * (L.card : ℝ) / (p : ℝ) := by
  sorry

end IncidenceBounds
