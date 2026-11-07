/-
The balanced case for divisor lattices (blueprint, Theorem 2.4), conditional on the
strict expansion property.

`UpExpansion n` says that for every nonempty set `S` of divisors of rank `k` strictly below the
middle, and for every nonempty proper subset of the lower middle rank when `Ω(n)` is odd, the
upper shadow of `S` is strictly larger than `S`. For balanced `n` this is the core of Griggs's
theorem (Order 1, 1984); it fails for dominated `n`. We show that it implies that the maximum
antichains of `D(n)` are exactly its middle ranks, so `a(n)` is `1` or `2` according to the
parity of `Ω(n)`. The dual (downward) expansion is derived from the upward one via the
complementation `d ↦ n / d`.
-/
import DivisorAntichains.Shifting

open Finset

noncomputable section

open Classical

namespace DivisorAntichains

namespace Div

variable {n : ℕ}

/-- Complementation `d ↦ n / d` on the divisors of `n`. -/
def compl (hn : n ≠ 0) (d : Div n) : Div n :=
  ⟨n / d.1, Nat.mem_divisors.2 ⟨Nat.div_dvd_of_dvd (val_dvd d), hn⟩⟩

theorem compl_compl (hn : n ≠ 0) (d : Div n) : compl hn (compl hn d) = d :=
  Subtype.ext (Nat.div_div_self (val_dvd d) hn)

theorem compl_injective (hn : n ≠ 0) : Function.Injective (compl hn) := fun a b h => by
  rw [← compl_compl hn a, h, compl_compl]

theorem div_dvd_div_iff (hn : n ≠ 0) {d e : ℕ} (hd : d ∣ n) (he : e ∣ n) :
    n / d ∣ n / e ↔ e ∣ d := by
  have hpos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd)
    (Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hn))
  rw [Nat.dvd_div_iff_mul_dvd he]
  have hn' : n = n / d * d := (Nat.div_mul_cancel hd).symm
  set q := n / d
  rw [show n = q * d from hn', mul_comm e q, Nat.mul_dvd_mul_iff_left hpos]

theorem compl_le_compl_iff (hn : n ≠ 0) {a b : Div n} : compl hn a ≤ compl hn b ↔ b ≤ a :=
  div_dvd_div_iff hn (val_dvd a) (val_dvd b)

theorem rank_compl (hn : n ≠ 0) (d : Div n) :
    rank (compl hn d) + rank d = ArithmeticFunction.cardFactors n := by
  show ArithmeticFunction.cardFactors (n / d.1) + ArithmeticFunction.cardFactors d.1 = _
  rw [← ArithmeticFunction.cardFactors_mul (Nat.div_ne_zero_iff_of_dvd (val_dvd d) |>.2
    ⟨hn, val_ne_zero d⟩) (val_ne_zero d), Nat.div_mul_cancel (val_dvd d)]

theorem rank_le (d : Div n) : rank d ≤ ArithmeticFunction.cardFactors n := by
  have := rank_compl (ne_zero_of d) d
  omega

/-- Every divisor of positive rank has a lower cover. -/
theorem exists_lower_cover (y : Div n) (hy : 0 < rank y) :
    ∃ x : Div n, x ≤ y ∧ rank x + 1 = rank y := by
  have hy1 : y.1 ≠ 1 := by
    intro h
    simp [rank, h] at hy
  obtain ⟨l, hl, hly⟩ := Nat.exists_prime_and_dvd hy1
  have hx : y.1 / l ∈ n.divisors :=
    Nat.mem_divisors.2 ⟨dvd_trans (Nat.div_dvd_of_dvd hly) (val_dvd y), ne_zero_of y⟩
  refine ⟨⟨y.1 / l, hx⟩, Nat.div_dvd_of_dvd hly, ?_⟩
  show ArithmeticFunction.cardFactors (y.1 / l) + 1 = ArithmeticFunction.cardFactors y.1
  have hne : y.1 / l ≠ 0 := Nat.div_ne_zero_iff_of_dvd hly |>.2 ⟨val_ne_zero y, hl.ne_zero⟩
  conv_rhs => rw [← Nat.div_mul_cancel hly]
  rw [ArithmeticFunction.cardFactors_mul hne hl.ne_zero,
    ArithmeticFunction.cardFactors_apply_prime hl]

end Div

/-- **Strict upward expansion** of the divisor lattice below its middle. -/
def UpExpansion (n : ℕ) : Prop :=
  ∀ k (S : Finset (Div n)), S ⊆ level Div.rank k → S.Nonempty →
    (2 * k + 1 < ArithmeticFunction.cardFactors n ∨
      (2 * k + 1 = ArithmeticFunction.cardFactors n ∧ S ≠ level Div.rank k)) →
    S.card < (up Div.rank S k).card

variable {n : ℕ}

theorem midRank_eq_level : midRank n = level Div.rank (ArithmeticFunction.cardFactors n / 2) :=
  rfl

/-- Ranks `k` and `Ω(n) - k` have the same size. -/
theorem card_level_compl (hn : n ≠ 0) {k : ℕ} (hk : k ≤ ArithmeticFunction.cardFactors n) :
    (level Div.rank (ArithmeticFunction.cardFactors n - k) : Finset (Div n)).card =
      (level Div.rank k : Finset (Div n)).card := by
  refine Finset.card_bij' (fun d _ => Div.compl hn d) (fun d _ => Div.compl hn d) ?_ ?_ ?_ ?_
  · intro d hd
    rw [mem_level] at hd ⊢
    have := Div.rank_compl hn d
    omega
  · intro d hd
    rw [mem_level] at hd ⊢
    have := Div.rank_compl hn d
    omega
  · intro d _
    exact Div.compl_compl hn d
  · intro d _
    exact Div.compl_compl hn d

/-- Downward expansion above the middle follows from upward expansion by complementation. -/
theorem down_expansion (hn : n ≠ 0) (hE : UpExpansion n) (k : ℕ) (S : Finset (Div n))
    (hS : S ⊆ level Div.rank k) (hne : S.Nonempty)
    (hk : ArithmeticFunction.cardFactors n + 1 < 2 * k) :
    S.card < (down Div.rank S k).card := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hkN : k ≤ (ArithmeticFunction.cardFactors n) := by
    have := Div.rank_le x₀
    have := mem_level.1 (hS hx₀)
    omega
  set S' := S.image (Div.compl hn)
  have hS' : S' ⊆ level Div.rank ((ArithmeticFunction.cardFactors n) - k) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    rw [mem_level]
    have := Div.rank_compl hn x
    have := mem_level.1 (hS hx)
    omega
  have hcard : S'.card = S.card := Finset.card_image_of_injective _ (Div.compl_injective hn)
  have hlt := hE ((ArithmeticFunction.cardFactors n) - k) S' hS' ⟨_, Finset.mem_image_of_mem _ hx₀⟩ (Or.inl (by omega))
  have hle : (up Div.rank S' ((ArithmeticFunction.cardFactors n) - k)).card ≤ (down Div.rank S k).card := by
    refine Finset.card_le_card_of_injOn (Div.compl hn) ?_ (Div.compl_injective hn).injOn
    intro y hy
    rw [mem_coe, mem_up] at hy
    obtain ⟨hy1, x', hx', hxy⟩ := hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hx'
    rw [mem_coe, mem_down]
    refine ⟨?_, x, hx, ?_⟩
    · have := Div.rank_compl hn y
      omega
    · rw [← Div.compl_le_compl_iff hn, Div.compl_compl]
      exact hxy
  omega

/-- **Maximum antichains in the balanced case.** Under strict upward expansion, every maximum
antichain of `D(n)` is a middle rank. -/
theorem eq_middle_of_upExpansion (hn : n ≠ 0) (hE : UpExpansion n) {A : Finset (Div n)}
    (hA : IsMaxAntichain A) :
    A = level Div.rank (ArithmeticFunction.cardFactors n / 2) ∨
      (ArithmeticFunction.cardFactors n % 2 = 1 ∧
        A = level Div.rank (ArithmeticFunction.cardFactors n / 2 + 1)) := by
  apply eq_level_of_isMaxAntichain Div.rank_strictMono
  · intro B hB
    exact card_le_midRank hn B hB
  · intro k S hS hne hk
    exact hE k S hS hne (Or.inl hk)
  · intro k S hS hne hk
    exact down_expansion hn hE k S hS hne hk
  · intro hodd S hS hne hprop
    exact hE _ S hS hne (Or.inr ⟨by omega, hprop⟩)
  · intro hodd
    apply Finset.Subset.antisymm (Finset.filter_subset _ _)
    intro y hy
    have hy' := mem_level.1 hy
    obtain ⟨x, hxy, hx⟩ := Div.exists_lower_cover y (by omega)
    rw [mem_filter]
    exact ⟨hy, x, by rw [mem_level]; omega, hxy⟩
  · intro hodd
    have := card_level_compl hn (k := (ArithmeticFunction.cardFactors n) / 2) (Nat.div_le_self _ _)
    rw [show (ArithmeticFunction.cardFactors n) - (ArithmeticFunction.cardFactors n) / 2 = (ArithmeticFunction.cardFactors n) / 2 + 1 by omega] at this
    exact this
  · exact hA

theorem level_nonempty (hn : n ≠ 0) {k : ℕ} (hk : k ≤ ArithmeticFunction.cardFactors n) :
    (level Div.rank k : Finset (Div n)).Nonempty := by
  obtain ⟨S⟩ := nonempty_scd n hn
  have : NeZero n := ⟨hn⟩
  have h1 := S.rank_le (⊥ : Div n)
  have h2 := S.rank_bot_le Div.rank_strictMono (⊥ : Div n)
  have h3 : Div.rank (⊥ : Div n) = 0 := Div.rank_bot
  obtain ⟨y, -, hy⟩ := S.exists_rank (⊥ : Div n) k (by omega) (by omega)
  exact ⟨y, mem_level.2 hy⟩

/-- **The count in the balanced case.** Under strict upward expansion, `a(n) = 1` if `Ω(n)` is
even and `a(n) = 2` if `Ω(n)` is odd. -/
theorem a_of_upExpansion (hn : n ≠ 0) (hE : UpExpansion n) :
    a n = if ArithmeticFunction.cardFactors n % 2 = 0 then 1 else 2 := by
  have hmax : IsMaxAntichain (level Div.rank ((ArithmeticFunction.cardFactors n) / 2) : Finset (Div n)) :=
    isMaxAntichain_midRank hn
  unfold a
  split_ifs with heven
  · rw [Finset.card_eq_one]
    refine ⟨level Div.rank ((ArithmeticFunction.cardFactors n) / 2), ?_⟩
    ext s
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro hs
      rcases eq_middle_of_upExpansion hn hE hs with h | ⟨h, -⟩
      · exact h
      · omega
    · rintro rfl
      exact hmax
  · have hodd : (ArithmeticFunction.cardFactors n) % 2 = 1 := by omega
    have hmax' : IsMaxAntichain (level Div.rank ((ArithmeticFunction.cardFactors n) / 2 + 1) : Finset (Div n)) := by
      refine ⟨isAntichain_level Div.rank_strictMono _, fun t ht => ?_⟩
      have := card_le_midRank hn t ht
      have h2 := card_level_compl hn (k := (ArithmeticFunction.cardFactors n) / 2) (Nat.div_le_self _ _)
      rw [show (ArithmeticFunction.cardFactors n) - (ArithmeticFunction.cardFactors n) / 2 = (ArithmeticFunction.cardFactors n) / 2 + 1 by omega] at h2
      rw [midRank_eq_level] at this
      omega
    have hne : (level Div.rank ((ArithmeticFunction.cardFactors n) / 2) : Finset (Div n)) ≠ level Div.rank ((ArithmeticFunction.cardFactors n) / 2 + 1) := by
      intro h
      obtain ⟨y, hy⟩ := level_nonempty hn (k := (ArithmeticFunction.cardFactors n) / 2) (Nat.div_le_self _ _)
      have h1 := mem_level.1 hy
      rw [h] at hy
      have h2 := mem_level.1 hy
      omega
    rw [Finset.card_eq_two]
    refine ⟨_, _, hne, ?_⟩
    ext s
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · intro hs
      rcases eq_middle_of_upExpansion hn hE hs with h | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
    · rintro (rfl | rfl)
      · exact hmax
      · exact hmax'

end DivisorAntichains
