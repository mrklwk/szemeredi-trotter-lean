module
public import MathCollab.NormalizedIncidence
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.Data.Finset.Sum

@[expose] public section

/-! Arbitrary affine lines in K² are affine subspaces with one-dimensional direction.
Every such line has a graph or vertical normal form. The chosen normalization is
injective, so finite sets retain their exact line cardinality and incidence count. -/

noncomputable section
open Classical
open scoped BigOperators

namespace MathCollab.AffineNormalization
variable {K : Type*} [Field K]

/-- All affine lines in the plane, with no chosen coordinates or distinguished point. -/
abbrev Line (K : Type*) [Field K] :=
  {s : AffineSubspace K (K × K) // Module.finrank K s.direction = 1}

abbrev NormalForm (K : Type*) := (K × K) ⊕ K

def onNormalForm (q : K × K) : NormalForm K → Prop
  | Sum.inl l => IncidenceCounting.onGraph q l
  | Sum.inr c => q.1 = c

/-- A line admits a base point and a nonzero direction spanning all its points. -/
theorem exists_parametrization (l : Line K) :
    ∃ p v : K × K, v ≠ 0 ∧ ∀ q : K × K, q ∈ l.val ↔ ∃ t : K, q = p + t • v := by
  have hnb : l.val ≠ ⊥ := by
    intro h
    have hd := l.property
    rw [h, AffineSubspace.direction_bot] at hd
    simp at hd
  obtain ⟨p, hp⟩ := l.val.nonempty_iff_ne_bot.mpr hnb
  obtain ⟨v, hv, hspan⟩ := finrank_eq_one_iff'.mp l.property
  refine ⟨p, v.val, ?_, ?_⟩
  · intro hz
    exact hv (Subtype.ext hz)
  · intro q
    constructor
    · intro hq
      have hdir : q - p ∈ l.val.direction := l.val.vsub_mem_direction hq hp
      obtain ⟨t, ht⟩ := hspan ⟨q - p, hdir⟩
      have ht' : t • (v : K × K) = q - p := congrArg Subtype.val ht
      refine ⟨t, ?_⟩
      rw [ht']
      abel
    · rintro ⟨t, rfl⟩
      have hdir := l.val.direction.smul_mem t v.property
      simpa [add_comm] using l.val.vadd_mem_of_mem_direction hdir hp

/-- Graph and vertical normal forms cover every affine line over every field. -/
theorem exists_normalForm (l : Line K) :
    ∃ n : NormalForm K, ∀ q, q ∈ l.val ↔ onNormalForm q n := by
  obtain ⟨p, v, hv, hparam⟩ := exists_parametrization l
  by_cases hx : v.1 = 0
  · have hy : v.2 ≠ 0 := by
      intro hy
      exact hv (Prod.ext hx hy)
    refine ⟨Sum.inr p.1, ?_⟩
    intro q
    rw [hparam]
    change (∃ t : K, q = p + t • v) ↔ q.1 = p.1
    constructor
    · rintro ⟨t, rfl⟩
      simp [hx]
    · intro hq
      refine ⟨(q.2 - p.2) / v.2, ?_⟩
      apply Prod.ext
      · simpa [hx] using hq
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        rw [div_mul_cancel₀ _ hy]
        ring
  · refine ⟨Sum.inl (v.2 / v.1, p.2 - (v.2 / v.1) * p.1), ?_⟩
    intro q
    rw [hparam]
    change (∃ t : K, q = p + t • v) ↔ q.2 = (v.2 / v.1) * q.1 + (p.2 - (v.2 / v.1) * p.1)
    constructor
    · rintro ⟨t, rfl⟩
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      field_simp [hx]
      ring
    · intro hq
      refine ⟨(q.1 - p.1) / v.1, ?_⟩
      apply Prod.ext
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        rw [div_mul_cancel₀ _ hx]
        ring
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        rw [hq]
        ring

/-- A chosen representation, certified by the point-membership equivalence. -/
def normalForm (l : Line K) : NormalForm K := (exists_normalForm l).choose

theorem mem_normalForm (l : Line K) (q : K × K) : q ∈ l.val ↔ onNormalForm q (normalForm l) :=
  (exists_normalForm l).choose_spec q

theorem normalForm_injective : Function.Injective (normalForm (K := K)) := by
  intro l m h
  apply Subtype.ext
  apply AffineSubspace.ext
  intro q
  rw [mem_normalForm, mem_normalForm, h]

def forms (L : Finset (Line K)) : Finset (NormalForm K) := L.image normalForm

def graphs (L : Finset (Line K)) : Finset (K × K) := (forms L).toLeft

def verticals (L : Finset (Line K)) : Finset K := (forms L).toRight

/-- Exact line cardinality, without duplicates or losses. -/
theorem card_graphs_add_verticals (L : Finset (Line K)) :
    (graphs L).card + (verticals L).card = L.card := by
  rw [graphs, verticals, Finset.card_toLeft_add_card_toRight, forms,
    Finset.card_image_of_injective _ normalForm_injective]

/-- The number of pairs (point,line) with the point on the arbitrary affine line. -/
def incidenceCount (P : Finset (K × K)) (L : Finset (Line K)) : ℕ :=
  IncidenceCounting.count P L (fun q l => q ∈ l.val)

theorem count_forms (P : Finset (K × K)) (L : Finset (Line K)) :
    IncidenceCounting.count P (forms L) onNormalForm = incidenceCount P L := by
  unfold forms incidenceCount IncidenceCounting.count
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro l _
    congr 1
    apply Finset.filter_congr
    intro q _
    exact (mem_normalForm l q).symm
  · intro l _ m _ h
    exact normalForm_injective h

/-- Exact incidence-count preservation under the affine-line normalization. -/
theorem incidenceCount_eq_normalized (P : Finset (K × K)) (L : Finset (Line K)) :
    incidenceCount P L = NormalizedIncidence.incidenceCount P (graphs L) (verticals L) := by
  rw [← count_forms]
  have hsplit : forms L = (graphs L).disjSum (verticals L) := Finset.toLeft_disjSum_toRight.symm
  rw [hsplit]
  simp only [IncidenceCounting.count, NormalizedIncidence.incidenceCount, Finset.sum_disjSum, onNormalForm]
  congr 1

end MathCollab.AffineNormalization

#print axioms MathCollab.AffineNormalization.exists_normalForm
#print axioms MathCollab.AffineNormalization.normalForm_injective
#print axioms MathCollab.AffineNormalization.incidenceCount_eq_normalized
