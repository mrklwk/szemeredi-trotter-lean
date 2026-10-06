module
public import MathCollab.Parameterized

@[expose] public section

/-! Exact Szemerédi–Trotter bounds for distinct graph and vertical lines.
All family, multiplicity, exceptional-set and optimization inputs are proved.
The separate affine-line normalization module supplies arbitrary lines. -/

noncomputable section
open Classical

namespace MathCollab.NormalizedIncidence

open IncidenceCounting
variable {K : Type*} [Field K]

def incidenceCount (P : Finset (K × K)) (L : Finset (K × K)) (V : Finset K) : ℕ :=
  count P L onGraph + count P V (fun q c => q.1 = c)

theorem empty_points (P : Finset (K × K)) (L : Finset (K × K)) (V : Finset K)
    (hP : P.card = 0) : incidenceCount P L V = 0 := by
  have hp := Finset.card_eq_zero.mp hP
  subst P
  simp [incidenceCount, count]

theorem only_vertical (P : Finset (K × K)) (L : Finset (K × K)) (V : Finset K)
    (hL : L.card = 0) : incidenceCount P L V ≤ P.card := by
  have hl := Finset.card_eq_zero.mp hL
  subst L
  simpa [incidenceCount, count] using vertical_count_le P V

/-- Exact characteristic-zero theorem for normalized distinct affine lines. -/
theorem exact_charZero [CharZero K] (P : Finset (K × K)) (L : Finset (K × K)) (V : Finset K) :
    (incidenceCount P L V : ℝ) ≤
      3 * ((P.card : ℝ) * (L.card + V.card : ℕ)) ^ ((2 : ℝ) / 3) +
        2 * P.card + (L.card + V.card : ℕ) := by
  apply IncidenceOptimization.exact_bound_charZero _ P.card L.card (L.card + V.card)
    (by omega) (empty_points P L V) (only_vertical P L V)
  intro d _
  exact Parameterized.discrete_bound P L V d (Or.inl ringChar.eq_zero)

/-- Exact positive-characteristic theorem. p is the field characteristic, never its size. -/
theorem exact_charP (p : ℕ) [CharP K p] (hp : p ≠ 0)
    (P : Finset (K × K)) (L : Finset (K × K)) (V : Finset K) :
    (incidenceCount P L V : ℝ) ≤
      3 * ((P.card : ℝ) * (L.card + V.card : ℕ)) ^ ((2 : ℝ) / 3) +
        2 * P.card + (L.card + V.card : ℕ) + 2 * P.card * (L.card + V.card : ℕ) / (p : ℝ) := by
  have hp2 := ((CharP.char_is_prime_or_zero K p).resolve_right hp).two_le
  apply IncidenceOptimization.exact_bound_positiveChar _ P.card L.card (L.card + V.card) p hp2
    (by omega) (empty_points P L V) (only_vertical P L V)
  intro d _ hdp
  exact Parameterized.discrete_bound P L V d (Or.inr (by simpa only [ringChar.eq K p] using hdp))

end MathCollab.NormalizedIncidence

#print axioms MathCollab.NormalizedIncidence.exact_charZero
#print axioms MathCollab.NormalizedIncidence.exact_charP
