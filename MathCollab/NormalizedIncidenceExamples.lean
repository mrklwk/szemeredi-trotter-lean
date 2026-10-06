module
public import MathCollab.NormalizedIncidence
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

noncomputable section
open Classical
namespace MathCollab.NormalizedIncidenceExamples
open NormalizedIncidence

example (L : Finset (ℚ × ℚ)) (V : Finset ℚ) : incidenceCount ∅ L V = 0 :=
  empty_points ∅ L V rfl

example (P : Finset (ZMod 2 × ZMod 2)) (V : Finset (ZMod 2)) :
    incidenceCount P ∅ V ≤ P.card := only_vertical P ∅ V rfl

example (P : Finset (ℚ × ℚ)) : incidenceCount P ∅ ∅ = 0 := by
  simp [incidenceCount, IncidenceCounting.count]

-- Four graph lines and two vertical lines over F₂ give twelve incidences on all four points.
example : incidenceCount
    ({(0, 0), (0, 1), (1, 0), (1, 1)} : Finset (ZMod 2 × ZMod 2))
    {(0, 0), (0, 1), (1, 0), (1, 1)} {0, 1} = 12 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  norm_num [h2, incidenceCount, IncidenceCounting.count, IncidenceCounting.onGraph,
    Finset.filter_insert, Finset.filter_singleton]
  simp only [h2]
  norm_num

-- The final positive-characteristic theorem explicitly includes p=2.
example (P L : Finset (ZMod 2 × ZMod 2)) (V : Finset (ZMod 2)) :
    (incidenceCount P L V : ℝ) ≤
      3 * ((P.card : ℝ) * (L.card + V.card : ℕ)) ^ ((2 : ℝ) / 3) +
        2 * P.card + (L.card + V.card : ℕ) + 2 * P.card * (L.card + V.card : ℕ) / (2 : ℝ) :=
  exact_charP 2 (by decide) P L V

end MathCollab.NormalizedIncidenceExamples
