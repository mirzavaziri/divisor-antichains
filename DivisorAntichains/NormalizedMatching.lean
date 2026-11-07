/-
Strict unimodality of the rank numbers of a balanced divisor lattice, and the reduction of
the strict expansion property to normalized matching.

Write `N_k(n)` for the number of divisors of `n` of rank `k`. For every `n` the sequence
`N_k(n)` is symmetric and weakly increases up to the middle. We prove that it increases
*strictly* up to the middle when `n` is balanced, i.e. when `2 v_q(n) ≤ Ω(n)` for every
prime `q`. Combined with the normalized matching property of `D(n)` (Hsieh–Kleitman, Harper),
which we state as a hypothesis, this gives strict upward expansion strictly below the middle.
When `Ω(n)` is even this is all of `UpExpansion n`; when `Ω(n)` is odd one more step, between
the two middle ranks, is still needed and is kept as a separate hypothesis.
-/
import DivisorAntichains.Balanced

open Finset

noncomputable section

open Classical

namespace DivisorAntichains

/-! ### Weak unimodality from a symmetric chain decomposition -/

namespace SCD

variable {P : Type*} [PartialOrder P] [Fintype P] {r : P → ℕ} {N : ℕ} (S : SCD P r N)

include S in
/-- Below the middle, moving one step up along the chains is injective on a rank. -/
theorem card_level_le_succ (hr : StrictMono r) {k : ℕ} (hk : 2 * k + 1 ≤ N) :
    (level r k).card ≤ (level r (k + 1)).card := by
  have hspec : ∀ x ∈ level r k, S.bot (S.pick x (k + 1)) = S.bot x ∧ r (S.pick x (k + 1)) = k + 1 :=
    fun x hx => by
      have h1 := mem_level.1 hx
      have h2 := S.rank_bot_le hr x
      exact S.pick_spec (by omega) (by omega)
  refine Finset.card_le_card_of_injOn (fun x => S.pick x (k + 1)) ?_ ?_
  · intro x hx
    rw [mem_coe] at hx ⊢
    exact mem_level.2 (hspec x hx).2
  · intro x hx y hy hxy
    rw [mem_coe] at hx hy
    have hb : S.bot x = S.bot y := by
      rw [← (hspec x hx).1, ← (hspec y hy).1]
      exact congrArg S.bot hxy
    exact S.eq_of_rank_eq hr hb ((mem_level.1 hx).trans (mem_level.1 hy).symm)

end SCD

/-! ### Rank numbers of divisor lattices -/

/-- The number of divisors of `n` of rank `k`. -/
def lv (n k : ℕ) : ℕ := (level Div.rank k : Finset (Div n)).card

variable {n : ℕ}

theorem lv_le_succ (hn : n ≠ 0) {k : ℕ} (hk : 2 * k + 1 ≤ ArithmeticFunction.cardFactors n) :
    lv n k ≤ lv n (k + 1) := by
  obtain ⟨S⟩ := nonempty_scd n hn
  exact S.card_level_le_succ Div.rank_strictMono hk

theorem lv_symm (hn : n ≠ 0) {k : ℕ} (hk : k ≤ ArithmeticFunction.cardFactors n) :
    lv n (ArithmeticFunction.cardFactors n - k) = lv n k :=
  card_level_compl hn hk

theorem lv_pos (hn : n ≠ 0) {k : ℕ} (hk : k ≤ ArithmeticFunction.cardFactors n) :
    0 < lv n k :=
  Finset.card_pos.2 (level_nonempty hn hk)

/-- Unimodality and symmetry: if `a ≤ b` and `a + b ≤ Ω(n)` then `N_a ≤ N_b`. -/
theorem lv_le_of_le (hn : n ≠ 0) :
    ∀ b a : ℕ, a ≤ b → a + b ≤ ArithmeticFunction.cardFactors n → lv n a ≤ lv n b := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro a hab habN
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_rfl
    · by_cases hmid : 2 * (b - 1) + 1 ≤ ArithmeticFunction.cardFactors n
      · have h1 := ih (b - 1) (by omega) a (by omega) (by omega)
        have h2 := lv_le_succ hn hmid
        rw [show b - 1 + 1 = b by omega] at h2
        exact h1.trans h2
      · -- reflect `b` to `Ω(n) - b`, which lies between `a` and `b`
        have hs := lv_symm hn (k := b) (by omega)
        rw [← hs]
        exact ih _ (by omega) a (by omega) (by omega)

/-! ### Peeling off one prime -/

section Peel

variable {p m L : ℕ}

theorem card_prod_level (k : ℕ) :
    (univ.filter fun z : Div m × Fin (L + 1) => Div.rank z.1 + (z.2 : ℕ) = k).card =
      ∑ j ∈ range (L + 1), (univ.filter fun d : Div m => Div.rank d + j = k).card := by
  rw [card_eq_sum_card_fiberwise (f := fun z : Div m × Fin (L + 1) => (z.2 : ℕ))
    (t := range (L + 1)) (fun z _ => by simp [z.2.isLt])]
  refine sum_congr rfl fun j hj => ?_
  refine Finset.card_bij (fun z _ => z.1) ?_ ?_ ?_
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz ⊢
    rw [← hz.2]
    exact hz.1
  · intro z hz w hw hzw
    simp only [mem_filter, mem_univ, true_and] at hz hw
    exact Prod.ext hzw (Fin.ext (hz.2.trans hw.2.symm))
  · intro d hd
    simp only [mem_filter, mem_univ, true_and] at hd
    refine ⟨(d, ⟨j, mem_range.1 hj⟩), ?_, rfl⟩
    simp [hd]

theorem lv_eq_card_prod (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m ≠ 0) (k : ℕ) :
    lv (p ^ L * m) k =
      (univ.filter fun z : Div m × Fin (L + 1) => Div.rank z.1 + (z.2 : ℕ) = k).card := by
  symm
  refine Finset.card_bij (fun z _ => decomp hp hpm hm z) ?_ ?_ ?_
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz
    rw [mem_level, rank_decomp]
    exact hz
  · intro z _ w _ h
    exact (decomp hp hpm hm).injective h
  · intro y hy
    refine ⟨(decomp hp hpm hm).symm y, ?_, by simp⟩
    simp only [mem_filter, mem_univ, true_and]
    rw [← rank_decomp hp hpm hm, OrderIso.apply_symm_apply]
    exact mem_level.1 hy

/-- The recursion `N_{k+1}(p^L m) + N_{k-L}(m) = N_k(p^L m) + N_{k+1}(m)`. -/
theorem lv_peel (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m ≠ 0) (k : ℕ) :
    lv (p ^ L * m) (k + 1) + (univ.filter fun d : Div m => Div.rank d + L = k).card =
      lv (p ^ L * m) k + lv m (k + 1) := by
  rw [lv_eq_card_prod hp hpm hm, lv_eq_card_prod hp hpm hm, card_prod_level, card_prod_level,
    sum_range_succ', sum_range_succ]
  have hshift : ∀ j ∈ range L, (univ.filter fun d : Div m => Div.rank d + (j + 1) = k + 1).card =
      (univ.filter fun d : Div m => Div.rank d + j = k).card := by
    intro j _
    congr 1
  rw [sum_congr rfl hshift]
  have h0 : (univ.filter fun d : Div m => Div.rank d + 0 = k + 1).card = lv m (k + 1) := by
    simp [lv, level]
  rw [h0]
  ac_rfl

theorem card_rank_add_eq (L k : ℕ) :
    (univ.filter fun d : Div m => Div.rank d + L = k).card =
      if L ≤ k then lv m (k - L) else 0 := by
  split_ifs with h
  · simp only [lv, level]
    congr 1
    ext d
    simp only [mem_filter, mem_univ, true_and]
    omega
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro d _
    omega

end Peel

/-! ### Strict increase -/

/-- **Strict increase of rank numbers.** If `k + v_q(n) < Ω(n)` for every prime `q` and `k` is
strictly below the middle, then `N_k(n) < N_{k+1}(n)`. -/
theorem lv_lt_succ : ∀ n : ℕ, n ≠ 0 → ∀ k : ℕ,
    (∀ q, k + n.factorization q < ArithmeticFunction.cardFactors n) →
    2 * k + 1 < ArithmeticFunction.cardFactors n → lv n k < lv n (k + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn k hq hk
    by_cases h1 : n = 1
    · subst h1
      rw [ArithmeticFunction.cardFactors_one] at hk
      omega
    set p := n.minFac
    have hp : p.Prime := Nat.minFac_prime h1
    set L := n.factorization p
    set m := n / p ^ L
    have hpm : ¬ p ∣ m := Nat.not_dvd_ordCompl hp hn
    have hn' : n = p ^ L * m := (Nat.ordProj_mul_ordCompl_eq_self n p).symm
    have hm : m ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hn'
      exact hn hn'
    have hL : 0 < L := hp.factorization_pos_of_dvd hn (Nat.minFac_dvd n)
    have hmn : m < n := by
      rw [hn']
      have : 1 < p ^ L := Nat.one_lt_pow hL.ne' hp.one_lt
      calc m = 1 * m := (one_mul m).symm
        _ < p ^ L * m := Nat.mul_lt_mul_of_pos_right this (Nat.pos_of_ne_zero hm)
    have hΩ : ArithmeticFunction.cardFactors m + L = ArithmeticFunction.cardFactors n := by
      rw [hn', ArithmeticFunction.cardFactors_mul (pow_ne_zero _ hp.ne_zero) hm,
        ArithmeticFunction.cardFactors_pow, ArithmeticFunction.cardFactors_apply_prime hp]
      ring
    have hfac : ∀ q, m.factorization q = if q = p then 0 else n.factorization q := by
      intro q
      have hmf : m.factorization = n.factorization.erase p := Nat.factorization_ordCompl n p
      rw [hmf]
      split_ifs with hqp
      · rw [hqp, Finsupp.erase_same]
      · rw [Finsupp.erase_ne hqp]
    have hpeel := lv_peel (L := L) hp hpm hm k
    rw [card_rank_add_eq, ← hn'] at hpeel
    have hqp := hq p
    split_ifs at hpeel with hLk
    · -- `L ≤ k`: use the induction hypothesis for `m` at `i = k - L`
      have hi : lv m (k - L) < lv m (k - L + 1) := by
        refine ih m hmn hm (k - L) (fun q => ?_) (by omega)
        rw [hfac q]
        split_ifs with hqp'
        · omega
        · have := hq q
          omega
      have hb := lv_le_of_le hm (k + 1) (k - L + 1) (by omega) (by omega)
      omega
    · -- `k < L`: the new chains start at rank `k + 1`
      have := lv_pos hm (k := k + 1) (by omega)
      omega

/-- `n` is balanced if no prime exponent exceeds half of `Ω(n)`. -/
def Balanced (n : ℕ) : Prop := ∀ q, 2 * n.factorization q ≤ ArithmeticFunction.cardFactors n

/-- **Strict unimodality in the balanced case.** -/
theorem lv_lt_succ_of_balanced (hn : n ≠ 0) (hb : Balanced n) {k : ℕ}
    (hk : 2 * k + 1 < ArithmeticFunction.cardFactors n) : lv n k < lv n (k + 1) :=
  lv_lt_succ n hn k (fun q => by have := hb q; omega) hk

/-! ### From normalized matching to strict expansion -/

/-- The **normalized matching property** of `D(n)`: for every set `S` of divisors of rank `k`,
`|∇S| / N_{k+1} ≥ |S| / N_k`. It holds for every `n` (Hsieh–Kleitman 1973, Harper 1974); here it
is a hypothesis. -/
def NormalizedMatching (n : ℕ) : Prop :=
  ∀ k (S : Finset (Div n)), S ⊆ level Div.rank k →
    S.card * lv n (k + 1) ≤ (up Div.rank S k).card * lv n k

/-- Strict expansion between the two middle ranks when `Ω(n)` is odd. -/
def MiddleExpansion (n : ℕ) : Prop :=
  ∀ S : Finset (Div n), S ⊆ level Div.rank (ArithmeticFunction.cardFactors n / 2) →
    S.Nonempty → S ≠ level Div.rank (ArithmeticFunction.cardFactors n / 2) →
    S.card < (up Div.rank S (ArithmeticFunction.cardFactors n / 2)).card

/-- Normalized matching and strict unimodality give strict expansion below the middle. -/
theorem card_lt_card_up (hn : n ≠ 0) (hb : Balanced n) (hNM : NormalizedMatching n) {k : ℕ}
    {S : Finset (Div n)} (hS : S ⊆ level Div.rank k) (hne : S.Nonempty)
    (hk : 2 * k + 1 < ArithmeticFunction.cardFactors n) : S.card < (up Div.rank S k).card := by
  have h1 := hNM k S hS
  have h2 := lv_lt_succ_of_balanced hn hb hk
  have h3 := Finset.card_pos.2 hne
  by_contra hcon
  push Not at hcon
  have : S.card * lv n (k + 1) ≤ S.card * lv n k :=
    h1.trans (Nat.mul_le_mul_right _ hcon)
  have := Nat.le_of_mul_le_mul_left this h3
  omega

theorem upExpansion_of_normalizedMatching (hn : n ≠ 0) (hb : Balanced n)
    (hNM : NormalizedMatching n)
    (hmid : ArithmeticFunction.cardFactors n % 2 = 1 → MiddleExpansion n) : UpExpansion n := by
  intro k S hS hne hk
  rcases hk with hk | ⟨hk, hfull⟩
  · exact card_lt_card_up hn hb hNM hS hne hk
  · have hk' : k = ArithmeticFunction.cardFactors n / 2 := by omega
    subst hk'
    exact hmid (by omega) S hS hne hfull

/-- **The balanced case, conditional on normalized matching.** -/
theorem a_of_normalizedMatching (hn : n ≠ 0) (hb : Balanced n) (hNM : NormalizedMatching n)
    (hmid : ArithmeticFunction.cardFactors n % 2 = 1 → MiddleExpansion n) :
    a n = if ArithmeticFunction.cardFactors n % 2 = 0 then 1 else 2 :=
  a_of_upExpansion hn (upExpansion_of_normalizedMatching hn hb hNM hmid)

/-- When `Ω(n)` is even, normalized matching alone forces the middle rank to be the unique
maximum antichain of a balanced divisor lattice. -/
theorem a_of_normalizedMatching_even (hn : n ≠ 0) (hb : Balanced n)
    (hNM : NormalizedMatching n) (heven : ArithmeticFunction.cardFactors n % 2 = 0) : a n = 1 := by
  rw [a_of_normalizedMatching hn hb hNM (fun h => by omega)]
  simp [heven]

end DivisorAntichains
