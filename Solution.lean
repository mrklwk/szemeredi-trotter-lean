module
public import MathCollab.IncidencePrimeAudit

/-! Completed proofs of the independently stated incidence bounds.
This module never imports Challenge. All theorem dependencies are checked. -/

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
  rw [← MathCollab.IncidencePrimeAudit.count_eq_pairs P L (fun q l => q ∈ l)]
  exact MathCollab.IncidenceSharper.affine_charZero P L hL

theorem arbitrary_charP {K : Type*} [Field K] (p : ℕ) [CharP K p] (hp : p ≠ 0)
    (P : Finset (K × K)) (L : Finset (AffineSubspace K (K × K)))
    (hL : ∀ l ∈ L, Module.finrank K l.direction = 1) :
    (((P ×ˢ L).filter (fun z => z.1 ∈ z.2)).card : ℝ) ≤
      3 * ((P.card : ℝ) * (L.card : ℝ)) ^ ((2 : ℝ) / 3) +
        (P.card : ℝ) + (L.card : ℝ) +
        2 * (P.card : ℝ) * (L.card : ℝ) / (p : ℝ) := by
  rw [← MathCollab.IncidencePrimeAudit.count_eq_pairs P L (fun q l => q ∈ l)]
  exact MathCollab.IncidenceSharper.affine_charP p hp P L hL

theorem subcritical {K : Type*} [Field K] (p : ℕ) [CharP K p] (hp : p ≠ 0)
    (P : Finset (K × K)) (L : Finset (AffineSubspace K (K × K)))
    (hL : ∀ l ∈ L, Module.finrank K l.direction = 1)
    (hcap : P.card * L.card ≤ p ^ 3) :
    (((P ×ˢ L).filter (fun z => z.1 ∈ z.2)).card : ℝ) ≤
      3 * ((P.card : ℝ) * (L.card : ℝ)) ^ ((2 : ℝ) / 3) +
        (P.card : ℝ) + (L.card : ℝ) := by
  rw [← MathCollab.IncidencePrimeAudit.count_eq_pairs P L (fun q l => q ∈ l)]
  exact MathCollab.IncidenceSubcritical.affine p hp P L hL hcap

theorem prime_field (p : ℕ) [Fact (Nat.Prime p)]
    (P : Finset (ZMod p × ZMod p))
    (L : Finset (AffineSubspace (ZMod p) (ZMod p × ZMod p)))
    (hL : ∀ l ∈ L, Module.finrank (ZMod p) l.direction = 1) :
    (((P ×ˢ L).filter (fun z => z.1 ∈ z.2)).card : ℝ) ≤
      3 * ((P.card : ℝ) * (L.card : ℝ)) ^ ((2 : ℝ) / 3) +
        (P.card : ℝ) + (L.card : ℝ) + (P.card : ℝ) * (L.card : ℝ) / (p : ℝ) := by
  rw [← MathCollab.IncidencePrimeAudit.count_eq_pairs P L (fun q l => q ∈ l)]
  exact MathCollab.IncidencePrime.affine p P L hL

end IncidenceBounds

#print axioms IncidenceBounds.arbitrary_charZero
#print axioms IncidenceBounds.arbitrary_charP
#print axioms IncidenceBounds.subcritical
#print axioms IncidenceBounds.prime_field
