module
public import MathCollab.IncidenceSubcritical
public import MathCollab.IncidenceTheoremExamples

@[expose] public section

noncomputable section
open Classical

namespace MathCollab.IncidenceSharperExamples
open AffineNormalization

-- Arbitrary affine lines over a characteristic-zero field: both linear coefficients are one.
example (P : Finset (ℚ × ℚ)) (L : Finset (AffineSubspace ℚ (ℚ × ℚ)))
    (hL : ∀ l ∈ L, Module.finrank ℚ l.direction = 1) :
    (IncidenceCounting.count P L (fun q l => q ∈ l) : ℝ) ≤
      3 * ((P.card : ℝ) * L.card) ^ ((2 : ℝ) / 3) + P.card + L.card :=
  IncidenceSharper.affine_charZero P L hL

-- The generic coordinate map remains valid in the smallest characteristic.
example : Function.Injective (GenericCoordinates.point (K := ZMod 2)) :=
  GenericCoordinates.point_injective

example (P : Finset (ZMod 2 × ZMod 2)) (L : Finset (Line (ZMod 2))) :
    (incidenceCount P L : ℝ) ≤
      3 * ((P.card : ℝ) * L.card) ^ ((2 : ℝ) / 3) + P.card + L.card +
        2 * P.card * L.card / (2 : ℝ) :=
  IncidenceSharper.lines_charP 2 (by decide) P L

example (P : Finset (RatFunc (ZMod 2) × RatFunc (ZMod 2)))
    (L : Finset (Line (RatFunc (ZMod 2)))) :
    (incidenceCount P L : ℝ) ≤
      3 * ((P.card : ℝ) * L.card) ^ ((2 : ℝ) / 3) + P.card + L.card +
        2 * P.card * L.card / (2 : ℝ) :=
  IncidenceSharper.lines_charP 2 (by decide) P L

-- Below mn≤p³ there is no characteristic term, including the equality boundary.
example (P : Finset (ZMod 2 × ZMod 2)) (L : Finset (Line (ZMod 2)))
    (h : P.card * L.card ≤ 8) :
    (incidenceCount P L : ℝ) ≤
      3 * ((P.card : ℝ) * L.card) ^ ((2 : ℝ) / 3) + P.card + L.card :=
  IncidenceSubcritical.lines 2 (by decide) P L h

example : 2 * (8 : ℝ) / ((IncidenceOptimization.clippedDegree 8 2 : ℝ) + 2) +
    (IncidenceOptimization.clippedDegree 8 2 : ℝ) ^ 2 ≤ 3 * (8 : ℝ) ^ ((2 : ℝ) / 3) :=
  IncidenceSubcritical.clipped_relaxed_le (by norm_num) (by norm_num) (by norm_num)

-- A vertical original line becomes a horizontal graph over the extension.
example (c : ZMod 2) : GenericCoordinates.graphOfNormalForm (Sum.inr c) = (0, RatFunc.C c) := rfl

-- The two mixed original lines still contribute exactly two incidences at the origin.
example : IncidenceCounting.count
    (GenericCoordinates.points ({(0, 0)} : Finset (ZMod 2 × ZMod 2)))
    (GenericCoordinates.lines
      {IncidenceTheoremExamples.horizontal, IncidenceTheoremExamples.vertical})
    IncidenceCounting.onGraph = 2 := by
  rw [GenericCoordinates.count_eq]
  simp [incidenceCount, IncidenceCounting.count, IncidenceTheoremExamples.horizontal_ne_vertical,
    IncidenceTheoremExamples.mem_horizontal, IncidenceTheoremExamples.mem_vertical, Finset.filter_singleton]

end MathCollab.IncidenceSharperExamples

#check MathCollab.IncidenceSharper.affine_charZero
#check MathCollab.IncidenceSharper.affine_charP
#check MathCollab.IncidenceSubcritical.affine
