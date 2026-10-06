module
public import MathCollab.IncidenceSubcritical
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-! The finite-plane incidence estimate from elementary second moments.
The parameter q is the cardinality of the field. No spectral or incidence bound
is assumed: line sizes, pair uniqueness, the variance estimate and Cauchy–Schwarz
are proved or applied explicitly below. -/

noncomputable section
open Classical
open scoped BigOperators

namespace MathCollab.FinitePlaneIncidence
open AffineNormalization IncidenceCounting
variable {K : Type*} [Field K] [Fintype K]

theorem line_card (l : NormalForm K) :
    ((Finset.univ : Finset (K × K)).filter (fun q => onNormalForm q l)).card = Fintype.card K := by
  rw [← Finset.card_univ (α := K)]
  cases l with
  | inl l =>
    apply Finset.card_bij (fun q _ => q.1)
    · intro q _
      simp
    · intro q hq r hr h
      apply Prod.ext h
      have hq' : q.2 = l.1 * q.1 + l.2 := (Finset.mem_filter.mp hq).2
      have hr' : r.2 = l.1 * r.1 + l.2 := (Finset.mem_filter.mp hr).2
      rw [hq', hr', h]
    · intro x _
      exact ⟨(x, l.1 * x + l.2), Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩
  | inr c =>
    apply Finset.card_bij (fun q _ => q.2)
    · intro q _
      simp
    · intro q hq r hr h
      exact Prod.ext ((Finset.mem_filter.mp hq).2.trans (Finset.mem_filter.mp hr).2.symm) h
    · intro y _
      exact ⟨(c, y), Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩

theorem normal_pair_unique (q r : K × K) (hqr : q ≠ r) (l k : NormalForm K)
    (hql : onNormalForm q l) (hrl : onNormalForm r l)
    (hqk : onNormalForm q k) (hrk : onNormalForm r k) : l = k := by
  cases l with
  | inl l =>
    cases k with
    | inl k =>
      exact congrArg Sum.inl (graph_pair_unique Finset.univ Finset.univ
        q (by simp) r (by simp) hqr l (by simp) k (by simp) hql hrl hqk hrk)
    | inr c =>
      have hx : q.1 = r.1 := hqk.trans hrk.symm
      have hy : q.2 = r.2 := by
        change q.2 = l.1 * q.1 + l.2 at hql
        change r.2 = l.1 * r.1 + l.2 at hrl
        rw [hql, hrl, hx]
      exact (hqr (Prod.ext hx hy)).elim
  | inr c =>
    cases k with
    | inl k =>
      have hx : q.1 = r.1 := hql.trans hrl.symm
      have hy : q.2 = r.2 := by
        change q.2 = k.1 * q.1 + k.2 at hqk
        change r.2 = k.1 * r.1 + k.2 at hrk
        rw [hqk, hrk, hx]
      exact (hqr (Prod.ext hx hy)).elim
    | inr d => exact congrArg Sum.inr (hql.symm.trans hqk)

theorem dual_pair_unique (L : Finset (NormalForm K)) :
    PairUnique L (Finset.univ : Finset (K × K)) (fun l q => onNormalForm q l) := by
  intro l _ k _ hlk q _ r _ hql hqk hrl hrk
  by_contra hqr
  exact hlk (normal_pair_unique q r hqr l k hql hrl hqk hrk)

theorem sum_degree (L : Finset (NormalForm K)) :
    (∑ q : K × K, degree L onNormalForm q) = Fintype.card K * L.card := by
  rw [← count_eq_sum_degree]
  simp only [count, line_card, Finset.sum_const, nsmul_eq_mul]
  simpa only [Nat.cast_id] using Nat.mul_comm L.card (Fintype.card K)

theorem square_eq_choose (r : ℕ) : r ^ 2 = 2 * r.choose 2 + r := by
  induction r with
  | zero => norm_num
  | succ r ih =>
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
    nlinarith

theorem sum_degree_sq (L : Finset (NormalForm K)) :
    (∑ q : K × K, (degree L onNormalForm q) ^ 2) ≤
      L.card ^ 2 + Fintype.card K * L.card := by
  have hc := sum_choose_degree_on_lines_le L (Finset.univ : Finset (K × K))
    (fun l q => onNormalForm q l) (dual_pair_unique L)
  change (∑ q : K × K, (degree L onNormalForm q).choose 2) ≤ L.card.choose 2 at hc
  simp_rw [square_eq_choose]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_degree]
  omega

def deviation (L : Finset (NormalForm K)) (q : K × K) : ℝ :=
  degree L onNormalForm q - (L.card : ℝ) / Fintype.card K

theorem variance_le (L : Finset (NormalForm K)) :
    (∑ q : K × K, deviation L q ^ 2) ≤ (Fintype.card K : ℝ) * L.card := by
  have hq : (Fintype.card K : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  have hfirst : (∑ q : K × K, (degree L onNormalForm q : ℝ)) =
      (Fintype.card K : ℝ) * L.card := by exact_mod_cast sum_degree L
  have hsecond : (∑ q : K × K, (degree L onNormalForm q : ℝ) ^ 2) ≤
      (L.card : ℝ) ^ 2 + Fintype.card K * L.card := by exact_mod_cast sum_degree_sq L
  have heq : (∑ q : K × K, deviation L q ^ 2) =
      (∑ q : K × K, (degree L onNormalForm q : ℝ) ^ 2) - (L.card : ℝ) ^ 2 := by
    simp only [deviation, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hfirst]
    field_simp [hq]
    ring
  rw [heq]
  linarith

theorem sum_deviation (P : Finset (K × K)) (L : Finset (NormalForm K)) :
    (∑ q ∈ P, deviation L q) = (count P L onNormalForm : ℝ) -
      (P.card : ℝ) * L.card / Fintype.card K := by
  simp only [deviation, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    count_eq_sum_degree, Nat.cast_sum]
  ring

/-- Vinh's numerical bound, proved here by finite-plane pair counts and variance. -/
theorem bound (P : Finset (K × K)) (L : Finset (NormalForm K)) :
    (count P L onNormalForm : ℝ) ≤ (P.card : ℝ) * L.card / Fintype.card K +
      Real.sqrt ((Fintype.card K : ℝ) * P.card * L.card) := by
  have hc := sq_sum_le_card_mul_sum_sq (s := P) (f := deviation L)
  have hsub : (∑ q ∈ P, deviation L q ^ 2) ≤ ∑ q : K × K, deviation L q ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ P) (by intro q _ _; positivity)
  have hv := mul_le_mul_of_nonneg_left (hsub.trans (variance_le L)) (Nat.cast_nonneg P.card : (0 : ℝ) ≤ P.card)
  rw [sum_deviation] at hc
  have hs : ((count P L onNormalForm : ℝ) - (P.card : ℝ) * L.card / Fintype.card K) ^ 2 ≤
      (Fintype.card K : ℝ) * P.card * L.card := by nlinarith [hc, hv]
  have h := Real.le_sqrt_of_sq_le hs
  linarith

theorem lines (P : Finset (K × K)) (L : Finset (Line K)) :
    (incidenceCount P L : ℝ) ≤ (P.card : ℝ) * L.card / Fintype.card K +
      Real.sqrt ((Fintype.card K : ℝ) * P.card * L.card) := by
  have h := bound P (forms L)
  have hcard : (forms L).card = L.card := Finset.card_image_of_injective _ normalForm_injective
  simpa only [count_forms, hcard] using h

end MathCollab.FinitePlaneIncidence

#print axioms MathCollab.FinitePlaneIncidence.variance_le
#print axioms MathCollab.FinitePlaneIncidence.lines
