/-
The squarefree case: Sperner's theorem with its characterization of the maximum antichains.

For squarefree `n` the divisor lattice is Boolean. Every divisor of rank `k` has exactly
`Ω(n) - k` upper covers and every divisor of rank `k + 1` has exactly `k + 1` lower covers, so
double counting gives `|S| (Ω(n) - k) ≤ |∇S| (k + 1)`. Below the middle this is strict
expansion. Between the two middle ranks of odd `Ω(n)`, equality forces every lower cover of
`∇S` back into `S`, and exchanging one prime at a time then sweeps out the whole rank. Hence
`UpExpansion n` holds without hypotheses, and `a(n)` is `1` or `2` according to the parity of
`Ω(n)`.
-/
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.NormNum.Prime
import DivisorAntichains.NormalizedMatching

open Finset

noncomputable section

open Classical

namespace DivisorAntichains

variable {n : ℕ}

/-- The upper covers of `d`. -/
def upCovers (d : Div n) : Finset (Div n) := univ.filter fun y => Div.rank y = Div.rank d + 1 ∧ d ≤ y

/-- The lower covers of `t`. -/
def lowCovers (t : Div n) : Finset (Div n) := univ.filter fun x => Div.rank x + 1 = Div.rank t ∧ x ≤ t

theorem mem_upCovers {d y : Div n} : y ∈ upCovers d ↔ Div.rank y = Div.rank d + 1 ∧ d ≤ y := by
  simp [upCovers]

theorem mem_lowCovers {t x : Div n} : x ∈ lowCovers t ↔ Div.rank x + 1 = Div.rank t ∧ x ≤ t := by
  simp [lowCovers]

theorem card_upCovers (hsq : Squarefree n) (d : Div n) :
    (upCovers d).card = ArithmeticFunction.cardFactors n - Div.rank d := by
  have hn : n ≠ 0 := Div.ne_zero_of d
  have hd0 := Div.val_ne_zero d
  have hdn := Div.val_dvd d
  have hnd0 : n / d.1 ≠ 0 := Nat.div_ne_zero_iff_of_dvd hdn |>.2 ⟨hn, hd0⟩
  have hcard : (n / d.1).primeFactors.card = ArithmeticFunction.cardFactors n - Div.rank d := by
    rw [← ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors,
      (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hnd0).2
        (hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hdn))]
    have := Div.rank_compl hn d
    simp only [Div.compl] at this
    exact Nat.eq_sub_of_add_eq this
  rw [← hcard]
  refine Finset.card_bij (fun y _ => y.1 / d.1) ?_ ?_ ?_
  · intro y hy
    rw [mem_upCovers] at hy
    have hdy : d.1 ∣ y.1 := hy.2
    have hy0 := Div.val_ne_zero y
    have hq0 : y.1 / d.1 ≠ 0 := Nat.div_ne_zero_iff_of_dvd hdy |>.2 ⟨hy0, hd0⟩
    rw [Nat.mem_primeFactors]
    refine ⟨?_, Nat.div_dvd_div hdy (Div.val_dvd y), hnd0⟩
    rw [← ArithmeticFunction.cardFactors_eq_one_iff_prime]
    have h := ArithmeticFunction.cardFactors_mul hd0 hq0
    rw [Nat.mul_div_cancel' hdy] at h
    have h1 : Div.rank y = ArithmeticFunction.cardFactors y.1 := rfl
    have h2 : Div.rank d = ArithmeticFunction.cardFactors d.1 := rfl
    omega
  · intro y hy y' hy' h
    rw [mem_upCovers] at hy hy'
    exact Subtype.ext ((Nat.div_left_inj hy.2 hy'.2).1 h)
  · intro q hq
    rw [Nat.mem_primeFactors] at hq
    obtain ⟨hqp, hqn, -⟩ := hq
    have hdq : d.1 * q ∣ n := Nat.mul_dvd_of_dvd_div hdn hqn
    set y : Div n := ⟨d.1 * q, Nat.mem_divisors.2 ⟨hdq, hn⟩⟩ with hy
    refine ⟨y, ?_, ?_⟩
    · rw [mem_upCovers]
      refine ⟨?_, Dvd.intro q rfl⟩
      show ArithmeticFunction.cardFactors (d.1 * q) = ArithmeticFunction.cardFactors d.1 + 1
      rw [ArithmeticFunction.cardFactors_mul hd0 hqp.ne_zero,
        ArithmeticFunction.cardFactors_apply_prime hqp]
    · exact Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero hd0)

theorem card_lowCovers (hsq : Squarefree n) (t : Div n) : (lowCovers t).card = Div.rank t := by
  have hn : n ≠ 0 := Div.ne_zero_of t
  have hc := card_upCovers hsq (Div.compl hn t)
  have hrt := Div.rank_compl hn t
  have hle := Div.rank_le t
  rw [show ArithmeticFunction.cardFactors n - Div.rank (Div.compl hn t) = Div.rank t by omega]
    at hc
  rw [← hc]
  refine Finset.card_bij (fun x _ => Div.compl hn x) ?_ ?_ ?_
  · intro x hx
    rw [mem_lowCovers] at hx
    rw [mem_upCovers]
    have := Div.rank_compl hn x
    refine ⟨by omega, (Div.compl_le_compl_iff hn).2 hx.2⟩
  · intro x _ y _ h
    exact Div.compl_injective hn h
  · intro y hy
    rw [mem_upCovers] at hy
    refine ⟨Div.compl hn y, ?_, Div.compl_compl hn y⟩
    rw [mem_lowCovers]
    have := Div.rank_compl hn y
    have := Div.rank_compl hn (Div.compl hn y)
    rw [Div.compl_compl] at this
    refine ⟨by omega, ?_⟩
    rw [← Div.compl_le_compl_iff hn, Div.compl_compl]
    exact hy.2

/-! ### Exchanging one prime -/

theorem dvd_of_primeFactors_subset {a b : ℕ} (ha : Squarefree a) (hb : b ≠ 0)
    (h : a.primeFactors ⊆ b.primeFactors) : a ∣ b := by
  rw [← Nat.prod_primeFactors_of_squarefree ha]
  exact (Nat.prod_primeFactors_dvd_iff hb).2 h

theorem exists_prime_dvd_not_dvd {a b : ℕ} (ha : Squarefree a) (hb : b ≠ 0) (h : ¬ a ∣ b) :
    ∃ q, q.Prime ∧ q ∣ a ∧ ¬ q ∣ b := by
  by_contra hcon
  push Not at hcon
  apply h
  refine dvd_of_primeFactors_subset ha hb fun q hq => ?_
  rw [Nat.mem_primeFactors] at hq ⊢
  exact ⟨hq.1, hcon q hq.1 hq.2.1, hb⟩

/-- The exchange step: if `S` contains every lower cover of every element of `∇S`, and `s ∈ S`,
`e` has the same rank as `s` but `s ≠ e`, then `S` contains an element closer to `e`. -/
theorem exchange (hsq : Squarefree n) {S : Finset (Div n)} {k : ℕ}
    (hclosed : ∀ t ∈ up Div.rank S k, ∀ x : Div n, Div.rank x + 1 = Div.rank t → x ≤ t → x ∈ S)
    {s e : Div n} (hs : s ∈ S) (hsk : Div.rank s = k) (he : Div.rank e = k) (hse : s ≠ e) :
    ∃ s' ∈ S, (e.1.primeFactors \ s'.1.primeFactors).card <
      (e.1.primeFactors \ s.1.primeFactors).card := by
  have hn : n ≠ 0 := Div.ne_zero_of s
  have hs0 := Div.val_ne_zero s
  have he0 := Div.val_ne_zero e
  have hsqe : Squarefree e.1 := hsq.squarefree_of_dvd (Div.val_dvd e)
  have hsqs : Squarefree s.1 := hsq.squarefree_of_dvd (Div.val_dvd s)
  have hnes : ¬ e.1 ∣ s.1 := fun h =>
    hse (eq_of_le_of_rank_le Div.rank_strictMono (show e ≤ s from h) (by omega)).symm
  have hnse : ¬ s.1 ∣ e.1 := fun h =>
    hse (eq_of_le_of_rank_le Div.rank_strictMono (show s ≤ e from h) (by omega))
  obtain ⟨q, hq, hqe, hqs⟩ := exists_prime_dvd_not_dvd hsqe hs0 hnes
  obtain ⟨p, hp, hps, hpe⟩ := exists_prime_dvd_not_dvd hsqs he0 hnse
  have hqn : q ∣ n := dvd_trans hqe (Div.val_dvd e)
  have hsq_n : s.1 * q ∣ n :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).2 hqs))
      (Div.val_dvd s) hqn
  set t : Div n := ⟨s.1 * q, Nat.mem_divisors.2 ⟨hsq_n, hn⟩⟩
  have hrt : Div.rank t = k + 1 := by
    show ArithmeticFunction.cardFactors (s.1 * q) = k + 1
    rw [ArithmeticFunction.cardFactors_mul hs0 hq.ne_zero,
      ArithmeticFunction.cardFactors_apply_prime hq]
    exact congrArg (· + 1) hsk
  have htup : t ∈ up Div.rank S k := mem_up.2 ⟨hrt, s, hs, Dvd.intro q rfl⟩
  have hsp0 : s.1 / p ≠ 0 := Nat.div_ne_zero_iff_of_dvd hps |>.2 ⟨hs0, hp.ne_zero⟩
  have hs't : s.1 / p * q ∣ s.1 * q := Nat.mul_dvd_mul_right (Nat.div_dvd_of_dvd hps) q
  set s' : Div n := ⟨s.1 / p * q, Nat.mem_divisors.2 ⟨dvd_trans hs't hsq_n, hn⟩⟩
  have hrs' : Div.rank s' + 1 = Div.rank t := by
    show ArithmeticFunction.cardFactors (s.1 / p * q) + 1 = ArithmeticFunction.cardFactors (s.1 * q)
    have h1 := ArithmeticFunction.cardFactors_mul hsp0 hp.ne_zero
    rw [Nat.div_mul_cancel hps, ArithmeticFunction.cardFactors_apply_prime hp] at h1
    rw [ArithmeticFunction.cardFactors_mul hsp0 hq.ne_zero,
      ArithmeticFunction.cardFactors_mul hs0 hq.ne_zero, h1]
    omega
  have hs'S : s' ∈ S := hclosed t htup s' hrs' hs't
  refine ⟨s', hs'S, Finset.card_lt_card ?_⟩
  have hs'0 : s.1 / p * q ≠ 0 := mul_ne_zero hsp0 hq.ne_zero
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨q, ?_, ?_⟩
    · rw [mem_sdiff, Nat.mem_primeFactors, Nat.mem_primeFactors]
      exact ⟨⟨hq, hqe, he0⟩, fun h => hqs h.2.1⟩
    · rw [mem_sdiff, Nat.mem_primeFactors, Nat.mem_primeFactors]
      exact fun h => h.2 ⟨hq, dvd_mul_left q _, hs'0⟩
  · intro r hr
    rw [mem_sdiff, Nat.mem_primeFactors, Nat.mem_primeFactors] at hr ⊢
    refine ⟨hr.1, fun h => hr.2 ⟨h.1, ?_, hs'0⟩⟩
    have hrp : r ≠ p := fun e' => hpe (e' ▸ hr.1.2.1)
    have hrdvd : r ∣ p * (s.1 / p) := by rw [Nat.mul_div_cancel' hps]; exact h.2.1
    rcases (Nat.Prime.dvd_mul h.1).1 hrdvd with h' | h'
    · exact absurd ((Nat.prime_dvd_prime_iff_eq h.1 hp).1 h') hrp
    · exact dvd_mul_of_dvd_left h' q

/-- If `S` is a nonempty set of rank `k` containing every lower cover of every element of its
upper shadow, then `S` is the whole rank. -/
theorem eq_level_of_closed (hsq : Squarefree n) {S : Finset (Div n)} {k : ℕ}
    (hS : S ⊆ level Div.rank k) (hne : S.Nonempty)
    (hclosed : ∀ t ∈ up Div.rank S k, ∀ x : Div n, Div.rank x + 1 = Div.rank t → x ≤ t → x ∈ S) :
    S = level Div.rank k := by
  refine Finset.Subset.antisymm hS fun e he => ?_
  rw [mem_level] at he
  obtain ⟨s, hs, hmin⟩ := Finset.exists_min_image S
    (fun s : Div n => (e.1.primeFactors \ s.1.primeFactors).card) hne
  by_cases hse : s = e
  · exact hse ▸ hs
  · obtain ⟨s', hs', hlt⟩ := exchange hsq hclosed hs (mem_level.1 (hS hs)) he hse
    exact absurd (hmin s' hs') (not_le.2 hlt)

/-! ### Strict expansion -/

/-- **Strict expansion in the squarefree case.** -/
theorem upExpansion_of_squarefree (hsq : Squarefree n) : UpExpansion n := by
  intro k S hS hne hk
  have hn : n ≠ 0 := hsq.ne_zero
  set T := up Div.rank S k
  have habove : ∀ a ∈ S, T.bipartiteAbove (· ≤ ·) a = upCovers a := by
    intro a ha
    ext y
    rw [mem_bipartiteAbove, mem_upCovers, mem_up, mem_level.1 (hS ha)]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, a, ha, h2⟩, h2⟩
  have hbelow : ∀ b ∈ T, S.bipartiteBelow (· ≤ ·) b ⊆ lowCovers b := by
    intro b hb x hx
    rw [mem_bipartiteBelow] at hx
    rw [mem_lowCovers, (mem_up.1 hb).1, mem_level.1 (hS hx.1)]
    exact ⟨rfl, hx.2⟩
  have hdegA : ∀ a ∈ S, (T.bipartiteAbove (· ≤ ·) a).card = ArithmeticFunction.cardFactors n - k := by
    intro a ha
    rw [habove a ha, card_upCovers hsq, mem_level.1 (hS ha)]
  have hdegB : ∀ b ∈ T, (S.bipartiteBelow (· ≤ ·) b).card ≤ k + 1 := by
    intro b hb
    have := card_le_card (hbelow b hb)
    rwa [card_lowCovers hsq, (mem_up.1 hb).1] at this
  have hsum := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := S) (t := T) (r := (· ≤ ·))
  rw [Finset.sum_congr rfl hdegA, Finset.sum_const, smul_eq_mul] at hsum
  have hS0 := Finset.card_pos.2 hne
  rcases hk with hk | ⟨hk, hfull⟩
  · -- below the middle
    have hle : S.card * (ArithmeticFunction.cardFactors n - k) ≤ T.card * (k + 1) := by
      rw [hsum]
      calc ∑ b ∈ T, (S.bipartiteBelow (· ≤ ·) b).card ≤ ∑ _b ∈ T, (k + 1) := sum_le_sum hdegB
        _ = T.card * (k + 1) := by rw [sum_const, smul_eq_mul]
    by_contra hcon
    push Not at hcon
    have h1 : S.card * (k + 1) < S.card * (ArithmeticFunction.cardFactors n - k) :=
      Nat.mul_lt_mul_of_pos_left (by omega) hS0
    have h2 : T.card * (k + 1) ≤ S.card * (k + 1) := Nat.mul_le_mul_right _ hcon
    omega
  · -- the two middle ranks
    have hdeg : ArithmeticFunction.cardFactors n - k = k + 1 := by omega
    rw [hdeg] at hsum
    by_contra hcon
    push Not at hcon
    apply hfull
    apply eq_level_of_closed hsq hS hne
    intro t ht x hx hxt
    by_contra hxS
    -- `t` has a lower cover outside `S`, so its degree into `S` is at most `k`
    have hlt : (S.bipartiteBelow (· ≤ ·) t).card < k + 1 := by
      have hsub : S.bipartiteBelow (· ≤ ·) t ⊂ lowCovers t := by
        rw [Finset.ssubset_iff_of_subset (hbelow t ht)]
        refine ⟨x, mem_lowCovers.2 ⟨hx, hxt⟩, fun h => hxS ((mem_bipartiteBelow _).1 h).1⟩
      have := card_lt_card hsub
      rwa [card_lowCovers hsq, (mem_up.1 ht).1] at this
    have hsumlt : ∑ b ∈ T, (S.bipartiteBelow (· ≤ ·) b).card < ∑ _b ∈ T, (k + 1) :=
      Finset.sum_lt_sum (fun b hb => hdegB b hb) ⟨t, ht, hlt⟩
    rw [sum_const, smul_eq_mul, ← hsum] at hsumlt
    have := Nat.mul_le_mul_right (k + 1) hcon
    omega

/-- **Maximum antichains of a squarefree divisor lattice** (Sperner's theorem with its
characterization of the extremal families): `a(n) = 1` if `Ω(n)` is even and `a(n) = 2` if it is
odd. -/
theorem a_of_squarefree (hsq : Squarefree n) :
    a n = if ArithmeticFunction.cardFactors n % 2 = 0 then 1 else 2 :=
  a_of_upExpansion hsq.ne_zero (upExpansion_of_squarefree hsq)

/-- Double counting the cover relation between `S` and its upper shadow. -/
theorem card_mul_eq_sum (hsq : Squarefree n) {S : Finset (Div n)} {k : ℕ}
    (hS : S ⊆ level Div.rank k) :
    S.card * (ArithmeticFunction.cardFactors n - k) =
      ∑ b ∈ up Div.rank S k, (S.bipartiteBelow (· ≤ ·) b).card := by
  have hdegA : ∀ a ∈ S, ((up Div.rank S k).bipartiteAbove (· ≤ ·) a).card =
      ArithmeticFunction.cardFactors n - k := by
    intro a ha
    have : (up Div.rank S k).bipartiteAbove (· ≤ ·) a = upCovers a := by
      ext y
      rw [mem_bipartiteAbove, mem_upCovers, mem_up, mem_level.1 (hS ha)]
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, a, ha, h2⟩, h2⟩
    rw [this, card_upCovers hsq, mem_level.1 (hS ha)]
  have hsum := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := S) (t := up Div.rank S k) (r := (· ≤ ·))
  rw [Finset.sum_congr rfl hdegA, Finset.sum_const, smul_eq_mul] at hsum
  exact hsum

theorem card_bipartiteBelow_le (hsq : Squarefree n) {S : Finset (Div n)} {k : ℕ}
    (hS : S ⊆ level Div.rank k) {b : Div n} (hb : b ∈ up Div.rank S k) :
    (S.bipartiteBelow (· ≤ ·) b).card ≤ k + 1 := by
  have hsub : S.bipartiteBelow (· ≤ ·) b ⊆ lowCovers b := by
    intro x hx
    rw [mem_bipartiteBelow] at hx
    rw [mem_lowCovers, (mem_up.1 hb).1, mem_level.1 (hS hx.1)]
    exact ⟨rfl, hx.2⟩
  have := card_le_card hsub
  rwa [card_lowCovers hsq, (mem_up.1 hb).1] at this

/-- Rank sizes of a Boolean divisor lattice: `N_k (Ω(n) - k) = N_{k+1} (k + 1)`. -/
theorem lv_mul_eq (hsq : Squarefree n) (k : ℕ) :
    lv n k * (ArithmeticFunction.cardFactors n - k) = lv n (k + 1) * (k + 1) := by
  have h := card_mul_eq_sum hsq (S := level Div.rank k) (k := k) (subset_refl _)
  have hup : up Div.rank (level Div.rank k : Finset (Div n)) k =
      (level Div.rank (k + 1) : Finset (Div n)) := by
    apply Finset.Subset.antisymm (Finset.filter_subset _ _)
    intro y hy
    obtain ⟨x, hxy, hx⟩ := Div.exists_lower_cover y (by rw [mem_level.1 hy]; omega)
    show y ∈ up Div.rank (level Div.rank k) k
    rw [mem_up]
    refine ⟨mem_level.1 hy, x, mem_level.2 (by rw [mem_level.1 hy] at hx; omega), hxy⟩
  have hdeg : ∀ b ∈ up Div.rank (level Div.rank k : Finset (Div n)) k,
      ((level Div.rank k : Finset (Div n)).bipartiteBelow (· ≤ ·) b).card = k + 1 := by
    intro b hb
    have : (level Div.rank k).bipartiteBelow (· ≤ ·) b = lowCovers b := by
      ext x
      rw [mem_bipartiteBelow, mem_lowCovers, mem_level, (mem_up.1 hb).1]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h2⟩
    rw [this, card_lowCovers hsq, (mem_up.1 hb).1]
  rw [Finset.sum_congr rfl hdeg, Finset.sum_const, smul_eq_mul, hup] at h
  simp only [lv]
  exact h

/-- **Normalized matching for squarefree `n`** (the local LYM inequality). -/
theorem normalizedMatching_of_squarefree (hsq : Squarefree n) : NormalizedMatching n := by
  intro k S hS
  have h1 := card_mul_eq_sum hsq hS
  have h2 : ∑ b ∈ up Div.rank S k, (S.bipartiteBelow (· ≤ ·) b).card ≤
      (up Div.rank S k).card * (k + 1) := by
    calc _ ≤ ∑ _b ∈ up Div.rank S k, (k + 1) :=
          sum_le_sum fun b hb => card_bipartiteBelow_le hsq hS hb
      _ = _ := by rw [sum_const, smul_eq_mul]
  have h3 := lv_mul_eq hsq k
  -- multiply the target by `k + 1` and use the two double countings
  apply Nat.le_of_mul_le_mul_right (c := k + 1) _ (Nat.succ_pos k)
  calc S.card * lv n (k + 1) * (k + 1) = S.card * (lv n (k + 1) * (k + 1)) := by ring
    _ = S.card * (lv n k * (ArithmeticFunction.cardFactors n - k)) := by rw [h3]
    _ = S.card * (ArithmeticFunction.cardFactors n - k) * lv n k := by ring
    _ ≤ (up Div.rank S k).card * (k + 1) * lv n k := Nat.mul_le_mul_right _ (h1 ▸ h2)
    _ = (up Div.rank S k).card * lv n k * (k + 1) := by ring

/-- `D(30)`: the two middle ranks are the only maximum antichains (A096826: `a(30) = 2`). -/
example : a 30 = 2 := by
  have hsq : Squarefree 30 := by
    rw [show (30 : ℕ) = 2 * 3 * 5 by norm_num]
    exact Nat.squarefree_mul_iff.2 ⟨by decide, Nat.squarefree_mul_iff.2 ⟨by decide,
      Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩, (by norm_num : Nat.Prime 5).squarefree⟩
  have hΩ : ArithmeticFunction.cardFactors 30 = 3 := by
    rw [show (30 : ℕ) = 2 * 3 * 5 by norm_num,
      ArithmeticFunction.cardFactors_mul (by norm_num) (by norm_num),
      ArithmeticFunction.cardFactors_mul (by norm_num) (by norm_num),
      ArithmeticFunction.cardFactors_apply_prime Nat.prime_two,
      ArithmeticFunction.cardFactors_apply_prime Nat.prime_three,
      ArithmeticFunction.cardFactors_apply_prime (by norm_num)]
  rw [a_of_squarefree hsq, hΩ]
  rfl

end DivisorAntichains
