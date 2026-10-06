module
public import MathCollab.IncidenceTheorem

@[expose] public section

/-! A generic coordinate change over K(t) sends all original lines to graphs.
It preserves points, distinct lines and actual incidence counts, in every
characteristic. No choice of a slope inside K or infinitude assumption is needed. -/

noncomputable section
open Classical

namespace MathCollab.GenericCoordinates
open AffineNormalization IncidenceCounting
variable {K : Type*} [Field K]

/-- The invertible coordinate change (x,y) ↦ (t*x+y,x), after embedding K into K(t). -/
def point (q : K × K) : RatFunc K × RatFunc K :=
  (RatFunc.X * RatFunc.C q.1 + RatFunc.C q.2, RatFunc.C q.1)

theorem point_injective : Function.Injective (point (K := K)) := by
  intro q r h
  have h₁ := congrArg Prod.snd h
  have h₂ := congrArg Prod.fst h
  change RatFunc.C q.1 = RatFunc.C r.1 at h₁
  change RatFunc.X * RatFunc.C q.1 + RatFunc.C q.2 =
    RatFunc.X * RatFunc.C r.1 + RatFunc.C r.2 at h₂
  rw [h₁] at h₂
  exact Prod.ext (RatFunc.C_injective h₁) (RatFunc.C_injective (add_left_cancel h₂))

theorem denominator_ne_zero (a : K) : RatFunc.X + RatFunc.C a ≠ (0 : RatFunc K) := by
  have hp : Polynomial.X + Polynomial.C a ≠ (0 : Polynomial K) := by
    intro h
    have hc := congrArg (fun f : Polynomial K => f.coeff 1) h
    simp at hc
  have h := RatFunc.algebraMap_ne_zero hp
  simpa only [map_add, RatFunc.algebraMap_X, RatFunc.algebraMap_C] using h

/-- A vertical original line becomes horizontal; an original graph has nonzero
generic denominator t+a. The resulting pair is its slope and intercept. -/
def graphOfNormalForm : NormalForm K → RatFunc K × RatFunc K
  | Sum.inl l => (1 / (RatFunc.X + RatFunc.C l.1),
      -(RatFunc.C l.2 / (RatFunc.X + RatFunc.C l.1)))
  | Sum.inr c => (0, RatFunc.C c)

theorem onGraph_iff (q : K × K) (n : NormalForm K) :
    onGraph (point q) (graphOfNormalForm n) ↔ onNormalForm q n := by
  cases n with
  | inl l =>
    change RatFunc.C q.1 = (1 / (RatFunc.X + RatFunc.C l.1)) *
      (RatFunc.X * RatFunc.C q.1 + RatFunc.C q.2) +
      -(RatFunc.C l.2 / (RatFunc.X + RatFunc.C l.1)) ↔ q.2 = l.1 * q.1 + l.2
    rw [← sub_eq_add_neg, one_div_mul_eq_div, ← sub_div,
      eq_div_iff (denominator_ne_zero l.1)]
    constructor
    · intro h
      apply RatFunc.C_injective
      simp only [map_add, map_mul]
      linear_combination -h
    · intro h
      have hc := congrArg (RatFunc.C (K := K)) h
      simp only [map_add, map_mul] at hc
      linear_combination -hc
  | inr c =>
    simpa only [point, graphOfNormalForm, onGraph, onNormalForm, zero_mul, zero_add]
      using (RatFunc.C_injective.eq_iff : RatFunc.C q.1 = RatFunc.C c ↔ q.1 = c)

def line (l : Line K) : RatFunc K × RatFunc K := graphOfNormalForm (normalForm l)

theorem mem_iff (q : K × K) (l : Line K) : onGraph (point q) (line l) ↔ q ∈ l.val :=
  (onGraph_iff q (normalForm l)).trans (mem_normalForm l q).symm

theorem line_injective : Function.Injective (line (K := K)) := by
  intro l k h
  apply Subtype.ext
  apply AffineSubspace.ext
  intro q
  rw [← mem_iff, ← mem_iff, h]

def points (P : Finset (K × K)) := P.image point
def lines (L : Finset (Line K)) := L.image line

theorem card_points (P : Finset (K × K)) : (points P).card = P.card :=
  Finset.card_image_of_injective _ point_injective

theorem card_lines (L : Finset (Line K)) : (lines L).card = L.card :=
  Finset.card_image_of_injective _ line_injective

/-- The generic coordinate change preserves the original incidence count exactly. -/
theorem count_eq (P : Finset (K × K)) (L : Finset (Line K)) :
    count (points P) (lines L) onGraph = incidenceCount P L := by
  unfold points lines count incidenceCount
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro l _
    rw [Finset.filter_image, Finset.card_image_of_injective _ point_injective]
    congr 1
    apply Finset.filter_congr
    intro q _
    exact mem_iff q l
  · intro l _ k _ h
    exact line_injective h

end MathCollab.GenericCoordinates

#print axioms MathCollab.GenericCoordinates.point_injective
#print axioms MathCollab.GenericCoordinates.line_injective
#print axioms MathCollab.GenericCoordinates.count_eq
