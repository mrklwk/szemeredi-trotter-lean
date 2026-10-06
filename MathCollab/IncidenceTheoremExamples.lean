module
public import MathCollab.IncidenceTheorem
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

noncomputable section
open Classical

namespace MathCollab.IncidenceTheoremExamples
open AffineNormalization IncidenceTheorem
variable {K : Type*} [Field K]

-- Empty sets have zero actual incidences, for arbitrary affine lines.
example (L : Finset (Line K)) : incidenceCount ∅ L = 0 := by
  simp [incidenceCount, IncidenceCounting.count]

example (P : Finset (K × K)) : incidenceCount P ∅ = 0 := by
  simp [incidenceCount, IncidenceCounting.count]

-- A nonzero direction constructs an arbitrary affine line, including vertical ones.
def lineThrough (p v : K × K) (hv : v ≠ 0) : Line K :=
  ⟨AffineSubspace.mk' p (Submodule.span K {v}), by
    rw [AffineSubspace.direction_mk']
    exact finrank_span_singleton hv⟩

def horizontal : Line K := lineThrough (0, 0) (1, 0) (by simp)
def vertical : Line K := lineThrough (0, 0) (0, 1) (by simp)

theorem mem_horizontal (q : K × K) : q ∈ (horizontal : Line K).val ↔ q.2 = 0 := by
  simp [horizontal, lineThrough, AffineSubspace.mem_mk', Submodule.mem_span_singleton,
    Prod.ext_iff, eq_comm]

theorem mem_vertical (q : K × K) : q ∈ (vertical : Line K).val ↔ q.1 = 0 := by
  simp [vertical, lineThrough, AffineSubspace.mem_mk', Submodule.mem_span_singleton,
    Prod.ext_iff, eq_comm]

theorem horizontal_ne_vertical : (horizontal : Line K) ≠ vertical := by
  intro h
  have hp : ((1, 0) : K × K) ∈ (horizontal : Line K).val := (mem_horizontal _).mpr rfl
  rw [h, mem_vertical] at hp
  exact one_ne_zero hp

-- One point lies on two distinct affine lines, including a vertical line, in every field.
example : incidenceCount ({(0, 0)} : Finset (K × K)) {horizontal, vertical} = 2 := by
  simp [incidenceCount, IncidenceCounting.count, horizontal_ne_vertical,
    mem_horizontal, mem_vertical, Finset.filter_singleton]

-- Characteristic two is included in the arbitrary-affine-subspace public interface.
example (P : Finset (ZMod 2 × ZMod 2))
    (L : Finset (AffineSubspace (ZMod 2) (ZMod 2 × ZMod 2)))
    (hL : ∀ l ∈ L, Module.finrank (ZMod 2) l.direction = 1) :
    (IncidenceCounting.count P L (fun q l => q ∈ l) : ℝ) ≤
      3 * ((P.card : ℝ) * L.card) ^ ((2 : ℝ) / 3) + 2 * P.card + L.card +
        2 * P.card * L.card / (2 : ℝ) :=
  affine_charP 2 (by decide) P L hL

-- This also works over an infinite positive-characteristic field, with no perfection hypothesis.
example (P : Finset (RatFunc (ZMod 2) × RatFunc (ZMod 2)))
    (L : Finset (Line (RatFunc (ZMod 2)))) :
    (incidenceCount P L : ℝ) ≤
      3 * ((P.card : ℝ) * L.card) ^ ((2 : ℝ) / 3) + 2 * P.card + L.card +
        2 * P.card * L.card / (2 : ℝ) :=
  szemeredi_trotter_charP 2 (by decide) P L

-- The characteristic-zero statement imposes no generic-position conditions.
example (P : Finset (ℚ × ℚ)) (L : Finset (AffineSubspace ℚ (ℚ × ℚ)))
    (hL : ∀ l ∈ L, Module.finrank ℚ l.direction = 1) :
    (IncidenceCounting.count P L (fun q l => q ∈ l) : ℝ) ≤
      3 * ((P.card : ℝ) * L.card) ^ ((2 : ℝ) / 3) + 2 * P.card + L.card :=
  affine_charZero P L hL

end MathCollab.IncidenceTheoremExamples

#check MathCollab.IncidenceTheorem.affine_charZero
#check MathCollab.IncidenceTheorem.affine_charP
