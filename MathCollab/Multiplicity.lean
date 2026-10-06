module
public import MathCollab.JetBudget
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Algebra.Squarefree.Basic

@[expose] public section

/-!
# The horizontal-line multiplicity bound

Contract D of `EXACT_CONTRACTS.md` (Lewko, arXiv:2609.27023v2, Lemma 3.1), horizontal
case. Let `K` be a field whose characteristic is `0` or exceeds `d`
(`ringChar K = 0 ∨ d < ringChar K`). Let `T ≠ 0` be squarefree with `deg T ≤ d`, let
`Y = b i` be distinct horizontal lines on none of which `T` vanishes identically, and let
`u^(ν i)` divide `T(ξ i + u, b i)`. Then `∑ i, (ν i - 1) ≤ d * (d - 1)` (natural subtraction).

Proof, following the paper:
1. `exists_yOnly_mul`: write `T = A * G` where `A` involves only `Y` and every `Y`-only
   divisor of `G` is a unit (descent on total degree; no factorization API needed).
2. On each line `A` restricts to a nonzero constant, so `u^(ν i)` divides `G(ξ i + u, b i)`.
3. If `G` is a unit, every `ν i = 0`. Otherwise `G` is squarefree, every irreducible factor
   `f` has `1 ≤ deg_X f ≤ d`, so `f_X ≠ 0` and `deg_X f_X < deg_X f` (this is where the
   characteristic hypothesis enters), whence `IsRelPrime G G_X` and `G_X ≠ 0`.
4. Restriction commutes with `∂/∂X`, so `u^(ν i - 1)` divides both restrictions of `G` and
   `G_X`; the jet budget gives `∑ (ν i - 1) ≤ deg G * deg G_X ≤ d * (d - 1)`.
-/

namespace MathCollab

open MvPolynomial

variable {K : Type*} [Field K]

/-! ### Restriction commutes with `∂/∂X` -/

theorem lineRestrict_pderiv_zero (ξ β : K) (P : MvPolynomial (Fin 2) K) :
    lineRestrict ξ β (pderiv 0 P) = Polynomial.derivative (lineRestrict ξ β P) := by
  induction P using MvPolynomial.induction_on with
  | C a => rw [pderiv_C, lineRestrict_C, map_zero, Polynomial.derivative_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, Polynomial.derivative_add]
  | mul_X p i hp =>
    rw [pderiv_mul, map_add, map_mul, map_mul, map_mul, hp, Polynomial.derivative_mul]
    congr 1
    fin_cases i
    · simp [lineRestrict_X_zero]
    · simp [lineRestrict_X_one, pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 by decide)]

/-! ### Polynomials in `Y` alone -/

/-- `D` involves only the variable `Y = X 1`. -/
def YOnly (D : MvPolynomial (Fin 2) K) : Prop :=
  ∃ q : MvPolynomial Unit K, rename (fun _ ↦ (1 : Fin 2)) q = D

theorem yOnly_one : YOnly (1 : MvPolynomial (Fin 2) K) := ⟨1, map_one _⟩

theorem YOnly.mul {A B : MvPolynomial (Fin 2) K} (hA : YOnly A) (hB : YOnly B) :
    YOnly (A * B) := by
  obtain ⟨p, rfl⟩ := hA
  obtain ⟨q, rfl⟩ := hB
  exact ⟨p * q, map_mul _ _ _⟩

/-- A `Y`-only polynomial restricts to a constant on every horizontal line. -/
theorem YOnly.lineRestrict_eq_C {A : MvPolynomial (Fin 2) K} (hA : YOnly A) (ξ β : K) :
    ∃ c : K, lineRestrict ξ β A = Polynomial.C c := by
  obtain ⟨q, rfl⟩ := hA
  refine ⟨eval (fun _ ↦ β) q, ?_⟩
  rw [lineRestrict, aeval_rename]
  induction q using MvPolynomial.induction_on with
  | C a => simp [Polynomial.algebraMap_eq]
  | add p q hp hq => rw [map_add, hp, hq, map_add, Polynomial.C_add]
  | mul_X p i hp => simp [hp, Polynomial.C_mul]

/-- A polynomial of `X`-degree zero involves only `Y`. -/
theorem yOnly_of_degreeOf_zero {D : MvPolynomial (Fin 2) K} (hD : degreeOf 0 D = 0) :
    YOnly D := by
  refine exists_rename_eq_of_vars_subset_range D _ (fun _ _ _ ↦ rfl) ?_
  intro i hi
  obtain ⟨m, hm, him⟩ := (mem_vars_iff_mem_support i).mp hi
  fin_cases i
  · exfalso
    have h1 := le_degreeOf_of_mem_support (0 : Fin 2) hm
    rw [Finsupp.mem_support_iff] at him
    simp only [Fin.zero_eta] at him
    omega
  · exact ⟨(), rfl⟩

/-- Every nonzero `T` factors as `A * G` with `A` involving only `Y` and no nonunit
`Y`-only divisor of `G`. -/
theorem exists_yOnly_mul {T : MvPolynomial (Fin 2) K} (hT : T ≠ 0) :
    ∃ A G, T = A * G ∧ YOnly A ∧ ∀ D, D ∣ G → YOnly D → IsUnit D := by
  suffices H : ∀ n (T : MvPolynomial (Fin 2) K), T ≠ 0 → T.totalDegree = n →
      ∃ A G, T = A * G ∧ YOnly A ∧ ∀ D, D ∣ G → YOnly D → IsUnit D from H _ T hT rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T hT hn
    by_cases hall : ∀ D, D ∣ T → YOnly D → IsUnit D
    · exact ⟨1, T, (one_mul T).symm, yOnly_one, hall⟩
    push Not at hall
    obtain ⟨D, ⟨T', rfl⟩, hDy, hDu⟩ := hall
    have hD0 : D ≠ 0 := left_ne_zero_of_mul hT
    have hT'0 : T' ≠ 0 := right_ne_zero_of_mul hT
    have hdeg := totalDegree_mul_of_isDomain hD0 hT'0
    have hDpos : 0 < D.totalDegree := by
      by_contra hz
      have hC := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_not_pos hz)
      have hc : D.coeff 0 ≠ 0 := fun h ↦ hD0 (by rw [hC, h, map_zero])
      exact hDu (hC ▸ (Ne.isUnit hc).map C)
    obtain ⟨A, G, hT', hA, hG⟩ := ih T'.totalDegree (by omega) T' hT'0 rfl
    exact ⟨D * A, G, by rw [hT', mul_assoc], hDy.mul hA, hG⟩

/-! ### The derivative in `X` under the characteristic hypothesis -/

theorem natCast_ne_zero_of_le {d n : ℕ} (hchar : ringChar K = 0 ∨ d < ringChar K)
    (h1 : 1 ≤ n) (hn : n ≤ d) : (n : K) ≠ 0 := by
  rw [Ne, ringChar.spec]
  rcases hchar with h | h
  · rw [h, zero_dvd_iff]; omega
  · intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega

theorem degreeOf_pderiv_zero_lt {f : MvPolynomial (Fin 2) K} (hf : 0 < degreeOf 0 f) :
    degreeOf 0 (pderiv 0 f) < degreeOf 0 f := by
  rw [degreeOf_lt_iff hf]
  intro m hm
  rw [mem_support_iff, coeff_pderiv] at hm
  have hmem : m + Finsupp.single 0 1 ∈ f.support :=
    mem_support_iff.mpr (left_ne_zero_of_mul hm)
  have := le_degreeOf_of_mem_support (0 : Fin 2) hmem
  simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
  omega

/-- If `1 ≤ deg_X f ≤ d` and the characteristic is `0` or exceeds `d`, then `f_X ≠ 0`. -/
theorem pderiv_zero_ne_zero {d : ℕ} (hchar : ringChar K = 0 ∨ d < ringChar K)
    {f : MvPolynomial (Fin 2) K} (hpos : 0 < degreeOf 0 f) (hle : degreeOf 0 f ≤ d) :
    pderiv 0 f ≠ 0 := by
  have hf0 : f ≠ 0 := ne_zero_of_degreeOf_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  have hne : f.support.Nonempty := support_nonempty.mpr hf0
  obtain ⟨m0, hm0, hsup⟩ := Finset.exists_mem_eq_sup f.support hne fun m ↦ m 0
  rw [← degreeOf_eq_sup] at hsup
  set m := m0 - Finsupp.single 0 1 with hmdef
  have hmm0 : m + Finsupp.single 0 1 = m0 := by
    ext k
    fin_cases k
    · simp [m]; omega
    · simp [m]
  intro hzero
  have hc : (pderiv 0 f).coeff m = 0 := by rw [hzero]; rfl
  rw [coeff_pderiv, hmm0] at hc
  have hm0' : m 0 + 1 = degreeOf 0 f := by
    rw [hsup, ← hmm0]; simp
  have hcast : ((m 0 : K) + 1) ≠ 0 := by
    have := natCast_ne_zero_of_le hchar (n := m 0 + 1) (by omega) (by omega)
    simpa using this
  exact (mul_ne_zero (mem_support_iff.mp hm0) hcast) hc

theorem totalDegree_pderiv_zero_add_one_le {G : MvPolynomial (Fin 2) K}
    (hGX : pderiv 0 G ≠ 0) : (pderiv 0 G).totalDegree + 1 ≤ G.totalDegree := by
  obtain ⟨m, hm, hsup⟩ := Finset.exists_mem_eq_sup (pderiv 0 G).support
    (support_nonempty.mpr hGX) fun s ↦ s.sum fun _ e ↦ e
  have htd : (pderiv 0 G).totalDegree = m.sum fun _ e ↦ e := hsup
  rw [mem_support_iff, coeff_pderiv] at hm
  have hmem : m + Finsupp.single 0 1 ∈ G.support :=
    mem_support_iff.mpr (left_ne_zero_of_mul hm)
  have hle := le_totalDegree hmem
  rw [Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl), Finsupp.sum_single_index rfl]
    at hle
  omega

/-- Squarefree `G` with no nonunit `Y`-only divisor and `deg G ≤ d < char` (or char `0`)
shares no nonunit factor with `G_X`. -/
theorem isRelPrime_pderiv_zero {d : ℕ} (hchar : ringChar K = 0 ∨ d < ringChar K)
    {G : MvPolynomial (Fin 2) K} (hG0 : G ≠ 0) (hsq : Squarefree G) (hdeg : G.totalDegree ≤ d)
    (hY : ∀ D, D ∣ G → YOnly D → IsUnit D) : IsRelPrime G (pderiv 0 G) := by
  intro D hDG hDGX
  by_contra hDu
  have hD0 : D ≠ 0 := by rintro rfl; exact hG0 (zero_dvd_iff.mp hDG)
  obtain ⟨f, hf, hfD⟩ := WfDvdMonoid.exists_irreducible_factor hDu hD0
  have hfG := hfD.trans hDG
  have hfGX := hfD.trans hDGX
  have hfpos : 0 < degreeOf 0 f := by
    by_contra h
    exact hf.not_isUnit (hY f hfG (yOnly_of_degreeOf_zero (by omega)))
  have hfle : degreeOf 0 f ≤ d :=
    (degreeOf_le_totalDegree f 0).trans ((totalDegree_le_of_dvd_of_isDomain hfG hG0).trans hdeg)
  obtain ⟨Q, rfl⟩ := hfG
  rw [pderiv_mul] at hfGX
  have hfdvd : f ∣ pderiv 0 f * Q := (dvd_add_left (dvd_mul_right f _)).mp hfGX
  rcases hf.prime.dvd_or_dvd hfdvd with h | h
  · have hne := pderiv_zero_ne_zero hchar hfpos hfle
    obtain ⟨c, hc⟩ := h
    have hc0 : c ≠ 0 := by rintro rfl; rw [mul_zero] at hc; exact hne hc
    have hdeg' := congrArg (degreeOf 0) hc
    rw [degreeOf_mul_eq hf.ne_zero hc0] at hdeg'
    have := degreeOf_pderiv_zero_lt hfpos
    omega
  · exact hf.not_isUnit (hsq f (mul_dvd_mul_left f h))

/-! ### The multiplicity bound -/

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- **Horizontal multiplicity bound (contract D).** Characteristic `0` or `d < char K`;
`T ≠ 0` squarefree of total degree `≤ d`; distinct horizontal lines `Y = b i` with
`T(ξ i + u, b i) ≠ 0`; `u^(ν i) ∣ T(ξ i + u, b i)`. Then `∑ (ν i - 1) ≤ d (d - 1)`. -/
theorem sum_sub_one_le_of_squarefree (ξ : J → K) {b : J → K} (hb : Function.Injective b)
    {d : ℕ} (hchar : ringChar K = 0 ∨ d < ringChar K) {T : MvPolynomial (Fin 2) K}
    (hT0 : T ≠ 0) (hsq : Squarefree T) (hdeg : T.totalDegree ≤ d) (ν : J → ℕ)
    (hres : ∀ i, lineRestrict (ξ i) (b i) T ≠ 0)
    (hdiv : ∀ i, Polynomial.X ^ ν i ∣ lineRestrict (ξ i) (b i) T) :
    ∑ i, (ν i - 1) ≤ d * (d - 1) := by
  obtain ⟨A, G, rfl, hA, hY⟩ := exists_yOnly_mul hT0
  have hG0 : G ≠ 0 := right_ne_zero_of_mul hT0
  -- Removing the `Y`-only factor preserves the divisibility on each line.
  have hdivG : ∀ i, Polynomial.X ^ ν i ∣ lineRestrict (ξ i) (b i) G := by
    intro i
    obtain ⟨c, hc⟩ := hA.lineRestrict_eq_C (ξ i) (b i)
    have h := hdiv i
    have hr := hres i
    rw [map_mul, hc] at h hr
    have hc0 : c ≠ 0 := by rintro rfl; simp at hr
    exact ((Ne.isUnit hc0).map Polynomial.C).dvd_mul_left.mp h
  by_cases hGu : IsUnit G
  · -- Unit `G`: each restriction is a nonzero constant, so every `ν i = 0`.
    have hzero : ∀ i, ν i = 0 := by
      intro i
      have hu : IsUnit (lineRestrict (ξ i) (b i) G) := hGu.map _
      have := Polynomial.natDegree_le_of_dvd (hdivG i) hu.ne_zero
      rwa [Polynomial.natDegree_X_pow, Polynomial.natDegree_eq_zero_of_isUnit hu,
        Nat.le_zero] at this
    simp [hzero]
  have hsqG : Squarefree G := hsq.squarefree_of_dvd (dvd_mul_left G A)
  have hdegG : G.totalDegree ≤ d :=
    (totalDegree_le_of_dvd_of_isDomain (dvd_mul_left G A) hT0).trans hdeg
  have hrel := isRelPrime_pderiv_zero hchar hG0 hsqG hdegG hY
  have hGX0 : pderiv 0 G ≠ 0 := by
    intro h
    rw [h, isRelPrime_zero_right] at hrel
    exact hGu hrel
  have hdegGX := totalDegree_pderiv_zero_add_one_le hGX0
  have hbudget := sum_le_totalDegree_mul_of_jets ξ hb (fun i ↦ ν i - 1) hG0 hGX0 hrel
    (fun i ↦ (pow_dvd_pow _ (Nat.sub_le _ _)).trans (hdivG i))
    (fun i ↦ by
      rw [lineRestrict_pderiv_zero]
      exact Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd (hdivG i))
  exact hbudget.trans (Nat.mul_le_mul hdegG (by omega))

/-- Characteristic-zero form of the horizontal multiplicity bound. -/
theorem sum_sub_one_le_of_squarefree_charZero [CharZero K] (ξ : J → K) {b : J → K}
    (hb : Function.Injective b) {d : ℕ} {T : MvPolynomial (Fin 2) K} (hT0 : T ≠ 0)
    (hsq : Squarefree T) (hdeg : T.totalDegree ≤ d) (ν : J → ℕ)
    (hres : ∀ i, lineRestrict (ξ i) (b i) T ≠ 0)
    (hdiv : ∀ i, Polynomial.X ^ ν i ∣ lineRestrict (ξ i) (b i) T) :
    ∑ i, (ν i - 1) ≤ d * (d - 1) :=
  sum_sub_one_le_of_squarefree ξ hb (Or.inl ringChar.eq_zero) hT0 hsq hdeg ν hres hdiv

/-- Positive-characteristic form: `p` is the characteristic of `K` and `d < p` (strict). -/
theorem sum_sub_one_le_of_squarefree_charP (p : ℕ) [CharP K p] (ξ : J → K) {b : J → K}
    (hb : Function.Injective b) {d : ℕ} (hdp : d < p) {T : MvPolynomial (Fin 2) K}
    (hT0 : T ≠ 0) (hsq : Squarefree T) (hdeg : T.totalDegree ≤ d) (ν : J → ℕ)
    (hres : ∀ i, lineRestrict (ξ i) (b i) T ≠ 0)
    (hdiv : ∀ i, Polynomial.X ^ ν i ∣ lineRestrict (ξ i) (b i) T) :
    ∑ i, (ν i - 1) ≤ d * (d - 1) :=
  sum_sub_one_le_of_squarefree ξ hb (Or.inr (ringChar.eq K p ▸ hdp)) hT0 hsq hdeg ν hres hdiv

end MathCollab
