module
public import MathCollab.IncidenceCounting
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! Empty sets, singleton points, characteristic two, and an explicit budget use. -/

noncomputable section
open scoped BigOperators
open Classical MathCollab.IncidenceCounting

variable {K : Type*} [Field K]

example (L : Finset (GraphLine K)) : count (∅ : Finset (K × K)) L onGraph = 0 := by
  simp [count]

example (P : Finset (K × K)) : count P (∅ : Finset (GraphLine K)) onGraph = 0 := by
  simp [count]

example (p : K × K) (L : Finset (GraphLine K)) : count {p} L onGraph ≤ L.card := by
  simpa using graph_count_le_card_lines_add_choose {p} L

-- The general proof includes characteristic two, without a field-size assumption.
example (P : Finset (ZMod 2 × ZMod 2)) (L : Finset (GraphLine (ZMod 2))) :
    count P L onGraph ≤ L.card + P.card.choose 2 :=
  graph_count_le_card_lines_add_choose P L

-- Empty exceptional set and zero excess: every selected point has degree ≤ e+1.
-- This exposes the exact condition consumed by the final bookkeeping theorem.
example (P : Finset (K × K)) (L : Finset (GraphLine K)) (V : Finset K) (e : ℕ)
    (h : ∀ p ∈ P, degree L onGraph p ≤ e + 1) :
    count P L onGraph + count P V (fun p c => p.1 = c) ≤
      P.card * (e + 2) + L.card := by
  have hbudget : (∑ p ∈ P \ ∅, (degree L onGraph p - e - 1)) ≤ 1 * (1 - 1) := by
    simp only [Finset.sdiff_empty, Nat.sub_self, Nat.mul_zero, Nat.le_zero]
    apply Finset.sum_eq_zero
    intro p hp
    have := h p hp
    omega
  simpa using graph_vertical_count_le_of_exceptional_budget P ∅ L V e 1
    (Finset.empty_subset P) (by simp) hbudget

-- All four points and all four graph lines over F₂ have eight incidences.
-- Enumerating the sets and expanding filters avoids reducing classical decisions.
example : count (Finset.univ : Finset (ZMod 2 × ZMod 2))
    (Finset.univ : Finset (GraphLine (ZMod 2))) onGraph = 8 := by
  have hu : (Finset.univ : Finset (ZMod 2 × ZMod 2)) =
      {(0, 0), (0, 1), (1, 0), (1, 1)} := by decide
  have htwo : (1 : ZMod 2) + 1 = 0 := by decide
  simp [count, onGraph, hu, Finset.filter_insert, Finset.filter_singleton, htwo]

example : count (Finset.univ : Finset (ZMod 2 × ZMod 2))
    (Finset.univ : Finset (ZMod 2)) (fun p c => p.1 = c) = 4 := by
  have hp : (Finset.univ : Finset (ZMod 2 × ZMod 2)) =
      {(0, 0), (0, 1), (1, 0), (1, 1)} := by decide
  have hv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  simp [count, hp, hv, Finset.filter_insert, Finset.filter_singleton]
