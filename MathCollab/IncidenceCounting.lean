module
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic

@[expose] public section

/-! Finite incidence bookkeeping for Section 4 of arXiv:2609.27023v2.
The final bookkeeping theorem is conditional on an explicit exceptional-set
size bound and excess budget; no polynomial or multiplicity result is assumed
to have been proved by this module. -/

noncomputable section
open scoped BigOperators
open Classical

namespace MathCollab.IncidenceCounting

variable {α β : Type*}

/-- Incidences counted by lines; finite sets contain no repeated points or lines. -/
def count (P : Finset α) (L : Finset β) (R : α → β → Prop) : ℕ := by
  classical
  exact ∑ l ∈ L, (P.filter fun p => R p l).card

/-- The number of lines through a point. -/
def degree (L : Finset β) (R : α → β → Prop) (p : α) : ℕ := by
  classical
  exact (L.filter (R p)).card

theorem count_eq_sum_degree (P : Finset α) (L : Finset β) (R : α → β → Prop) :
    count P L R = ∑ p ∈ P, degree L R p := by
  classical
  simp only [count, degree, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

/-- Any two distinct selected points have at most one selected common line. -/
def PairUnique (P : Finset α) (L : Finset β) (R : α → β → Prop) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, p ≠ q → ∀ l ∈ L, ∀ k ∈ L,
    R p l → R q l → R p k → R q k → l = k

theorem nat_le_one_add_choose_two (n : ℕ) : n ≤ 1 + n.choose 2 := by
  cases n with
  | zero => simp
  | succ n => rw [Nat.choose_succ_succ', Nat.choose_one_right]; omega

/-- Count unordered pairs on each line; uniqueness makes these pair sets disjoint. -/
theorem sum_choose_degree_on_lines_le (P : Finset α) (L : Finset β)
    (R : α → β → Prop) (hR : PairUnique P L R) :
    (∑ l ∈ L, ((P.filter fun p => R p l).card).choose 2) ≤ P.card.choose 2 := by
  classical
  let pairs (l : β) := (P.filter fun p => R p l).powersetCard 2
  have hd : (L : Set β).PairwiseDisjoint pairs := by
    intro l hl k hk hlk
    apply Finset.disjoint_left.mpr
    intro s hsl hsk
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hsl
    obtain ⟨hsub', _⟩ := Finset.mem_powersetCard.mp hsk
    obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hcard
    have hp := Finset.mem_filter.mp (hsub (Finset.mem_insert_self p {q}))
    have hq := Finset.mem_filter.mp (hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self q)))
    have hp' := Finset.mem_filter.mp (hsub' (Finset.mem_insert_self p {q}))
    have hq' := Finset.mem_filter.mp (hsub' (Finset.mem_insert_of_mem (Finset.mem_singleton_self q)))
    exact hlk (hR p hp.1 q hq.1 hpq l hl k hk hp.2 hq.2 hp'.2 hq'.2)
  have hs : L.biUnion pairs ⊆ P.powersetCard 2 := by
    intro s hs
    obtain ⟨l, _, hsl⟩ := Finset.mem_biUnion.mp hs
    exact Finset.powersetCard_mono (Finset.filter_subset _ _) hsl
  have hc := Finset.card_le_card hs
  rw [Finset.card_biUnion hd] at hc
  simpa only [pairs, Finset.card_powersetCard] using hc

/-- The exact exceptional-point bound: I(E,L) ≤ |L| + choose(|E|,2). -/
theorem count_le_card_lines_add_choose (P : Finset α) (L : Finset β)
    (R : α → β → Prop) (hR : PairUnique P L R) :
    count P L R ≤ L.card + P.card.choose 2 := by
  classical
  calc
    count P L R ≤ ∑ l ∈ L, (1 + ((P.filter fun p => R p l).card).choose 2) :=
      Finset.sum_le_sum fun _ _ => nat_le_one_add_choose_two _
    _ = L.card + ∑ l ∈ L, ((P.filter fun p => R p l).card).choose 2 := by
      rw [Finset.sum_add_distrib]; simp
    _ ≤ L.card + P.card.choose 2 :=
      Nat.add_le_add_left (sum_choose_degree_on_lines_le P L R hR) _

/-- If each point has at most one selected line, there are at most |P| incidences. -/
theorem count_le_card_points (P : Finset α) (L : Finset β) (R : α → β → Prop)
    (hR : ∀ p ∈ P, ∀ l ∈ L, ∀ k ∈ L, R p l → R p k → l = k) :
    count P L R ≤ P.card := by
  classical
  rw [count_eq_sum_degree]
  calc
    (∑ p ∈ P, degree L R p) ≤ ∑ _p ∈ P, 1 := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.card_le_one.mpr
      intro l hl k hk
      exact hR p hp l (Finset.mem_filter.mp hl).1 k (Finset.mem_filter.mp hk).1
        (Finset.mem_filter.mp hl).2 (Finset.mem_filter.mp hk).2
    _ = P.card := by simp

variable {K : Type*} [Field K]

/-- A nonvertical normalized line is its slope/intercept pair. -/
abbrev GraphLine (K : Type*) := K × K

def onGraph (p : K × K) (l : GraphLine K) : Prop := p.2 = l.1 * p.1 + l.2

theorem graph_pair_unique (P : Finset (K × K)) (L : Finset (GraphLine K)) :
    PairUnique P L onGraph := by
  intro p _ q _ hpq l _ k _ hpl hql hpk hqk
  change p.2 = l.1 * p.1 + l.2 at hpl
  change q.2 = l.1 * q.1 + l.2 at hql
  change p.2 = k.1 * p.1 + k.2 at hpk
  change q.2 = k.1 * q.1 + k.2 at hqk
  have hx : p.1 ≠ q.1 := by
    intro hx
    apply hpq
    apply Prod.ext hx
    rw [hpl, hql, hx]
  have hm : (l.1 - k.1) * (p.1 - q.1) = 0 := by
    linear_combination -hpl + hpk + hql - hqk
  have ha : l.1 = k.1 := sub_eq_zero.mp
    ((mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr hx))
  apply Prod.ext ha
  rw [ha] at hpl
  linear_combination hpk - hpl

theorem graph_count_le_card_lines_add_choose (P : Finset (K × K))
    (L : Finset (GraphLine K)) : count P L onGraph ≤ L.card + P.card.choose 2 :=
  count_le_card_lines_add_choose P L onGraph (graph_pair_unique P L)

omit [Field K] in
/-- Distinct vertical lines x=c contribute at most one incidence per point. -/
theorem vertical_count_le (P : Finset (K × K)) (V : Finset K) :
    count P V (fun p c => p.1 = c) ≤ P.card := by
  apply count_le_card_points
  intro p _ l _ k _ hl hk
  exact hl.symm.trans hk

theorem choose_two_le_allowance {h e : ℕ} (he : h ≤ e) :
    h.choose 2 ≤ h * (e + 1) := by
  rw [Nat.choose_two_right]
  exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left h (by omega))

/-- Pointwise excess gives the exact baseline-plus-budget bound. -/
theorem sum_degree_le_allowance (A : Finset α) (r : α → ℕ) (e B : ℕ)
    (hB : (∑ p ∈ A, (r p - e - 1)) ≤ B) :
    (∑ p ∈ A, r p) ≤ A.card * (e + 1) + B := by
  calc
    (∑ p ∈ A, r p) ≤ ∑ p ∈ A, (e + 1 + (r p - e - 1)) :=
      Finset.sum_le_sum fun p _ => by omega
    _ = A.card * (e + 1) + ∑ p ∈ A, (r p - e - 1) := by
      rw [Finset.sum_add_distrib]; simp
    _ ≤ A.card * (e + 1) + B := Nat.add_le_add_left hB _

/-- Conditional bookkeeping: the unproved algebraic inputs are explicit arguments. -/
theorem count_le_of_exceptional_budget [DecidableEq α] (P E : Finset α) (L : Finset β)
    (R : α → β → Prop) (e B : ℕ) (hEP : E ⊆ P)
    (hR : PairUnique E L R) (hE : E.card ≤ e)
    (hB : (∑ p ∈ P \ E, (degree L R p - e - 1)) ≤ B) :
    count P L R ≤ P.card * (e + 1) + B + L.card := by
  classical
  have hsplit : count P L R = count (P \ E) L R + count E L R := by
    simp only [count_eq_sum_degree]
    exact (Finset.sum_sdiff hEP).symm
  have hout := sum_degree_le_allowance (P \ E) (degree L R) e B hB
  rw [← count_eq_sum_degree] at hout
  have hin := count_le_card_lines_add_choose E L R hR
  have hchoose := choose_two_le_allowance hE
  have hcard := Finset.card_sdiff_add_card_eq_card hEP
  have hmul : (P \ E).card * (e + 1) + E.card * (e + 1) = P.card * (e + 1) := by
    rw [← Nat.add_mul, hcard]
  omega

/-- Section 4's exact discrete expression, conditional on its two algebraic inputs. -/
theorem graph_vertical_count_le_of_exceptional_budget
    (P E : Finset (K × K)) (L : Finset (GraphLine K)) (V : Finset K)
    (e d : ℕ) (hEP : E ⊆ P) (hE : E.card ≤ e)
    (hB : (∑ p ∈ P \ E, (degree L onGraph p - e - 1)) ≤ d * (d - 1)) :
    count P L onGraph + count P V (fun p c => p.1 = c) ≤
      P.card * (e + 2) + d * (d - 1) + L.card := by
  have hg := count_le_of_exceptional_budget P E L onGraph e (d * (d - 1))
    hEP (graph_pair_unique E L) hE hB
  have hv := vertical_count_le P V
  have hm : P.card * (e + 2) = P.card * (e + 1) + P.card := by ring
  omega

end MathCollab.IncidenceCounting

#print axioms MathCollab.IncidenceCounting.graph_count_le_card_lines_add_choose
#print axioms MathCollab.IncidenceCounting.vertical_count_le
#print axioms MathCollab.IncidenceCounting.graph_vertical_count_le_of_exceptional_budget
