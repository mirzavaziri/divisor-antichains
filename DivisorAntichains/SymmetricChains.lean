/-
Symmetric chain decompositions and the Sperner property of divisor lattices
(de Bruijn, van Ebbenhorst Tengbergen and Kruyswijk, 1951; blueprint Theorem 2.2).

A symmetric chain decomposition of a poset with rank function `r` and total rank `N` is
encoded by a map `bot` sending each element to the bottom of its chain: elements with the
same bottom are comparable, the chain of `b` occupies exactly the ranks `r b, ..., N - r b`.
We show that such decompositions are preserved by products with a chain and by
rank-preserving order isomorphisms, construct one for every divisor lattice, and deduce
that the width of `D(n)` is the size of its middle rank.
-/
import DivisorAntichains.Binomial

open Finset

noncomputable section

open Classical

namespace DivisorAntichains

/-- A symmetric chain decomposition of `P` with respect to the rank function `r` and the total
rank `N`, recorded through the bottom element of each chain. -/
structure SCD (P : Type*) [PartialOrder P] (r : P → ℕ) (N : ℕ) where
  /-- the bottom of the chain containing `x` -/
  bot : P → P
  bot_le : ∀ x, bot x ≤ x
  comparable : ∀ x y, bot x = bot y → x ≤ y ∨ y ≤ x
  rank_le : ∀ x, r x + r (bot x) ≤ N
  exists_rank : ∀ x k, r (bot x) ≤ k → k + r (bot x) ≤ N → ∃ y, bot y = bot x ∧ r y = k

namespace SCD

variable {P : Type*} [PartialOrder P] {r : P → ℕ} {N : ℕ} (S : SCD P r N)

theorem le_of_rank_le (hr : StrictMono r) {x y : P} (hxy : S.bot x = S.bot y) (h : r x ≤ r y) :
    x ≤ y := by
  rcases S.comparable x y hxy with h' | h'
  · exact h'
  · rcases eq_or_lt_of_le h' with e | e
    · exact e ▸ le_rfl
    · exact absurd (hr e) (not_lt.2 h)

theorem eq_of_rank_eq (hr : StrictMono r) {x y : P} (hxy : S.bot x = S.bot y) (h : r x = r y) :
    x = y :=
  le_antisymm (S.le_of_rank_le hr hxy h.le) (S.le_of_rank_le hr hxy.symm h.ge)

theorem rank_bot_le (hr : StrictMono r) (x : P) : r (S.bot x) ≤ r x := hr.monotone (S.bot_le x)

/-- The element of the chain of `x` with rank `k` (or `x` itself if there is none). -/
def pick (x : P) (k : ℕ) : P :=
  if h : r (S.bot x) ≤ k ∧ k + r (S.bot x) ≤ N then Classical.choose (S.exists_rank x k h.1 h.2)
  else x

theorem pick_spec {x : P} {k : ℕ} (h1 : r (S.bot x) ≤ k) (h2 : k + r (S.bot x) ≤ N) :
    S.bot (S.pick x k) = S.bot x ∧ r (S.pick x k) = k := by
  have h : r (S.bot x) ≤ k ∧ k + r (S.bot x) ≤ N := ⟨h1, h2⟩
  simp only [pick, h, and_self, dite_true]
  exact Classical.choose_spec (S.exists_rank x k h1 h2)

/-- Every chain meets the middle rank `N / 2`. -/
theorem exists_mid (hr : StrictMono r) (x : P) :
    ∃ y, S.bot y = S.bot x ∧ r y = N / 2 := by
  have h1 := S.rank_le x
  have h2 := S.rank_bot_le hr x
  exact S.exists_rank x (N / 2) (by omega) (by omega)

include S in
/-- **Sperner property.** If `P` has a symmetric chain decomposition, every antichain of `P` is
at most as large as the middle rank. -/
theorem card_le_mid [Fintype P] (hr : StrictMono r) (A : Finset P)
    (hA : IsAntichain (· ≤ ·) (A : Set P)) :
    A.card ≤ (univ.filter fun y : P => r y = N / 2).card := by
  refine Finset.card_le_card_of_injOn (fun x => Classical.choose (S.exists_mid hr x)) ?_ ?_
  · intro x _
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    exact (Classical.choose_spec (S.exists_mid hr x)).2
  · intro x hx y hy hxy
    have hx' := (Classical.choose_spec (S.exists_mid hr x)).1
    have hy' := (Classical.choose_spec (S.exists_mid hr y)).1
    simp only at hxy
    rw [hxy] at hx'
    have hb : S.bot x = S.bot y := hx'.symm.trans hy'
    by_contra hne
    rcases S.comparable x y hb with h | h
    · exact hA hx hy hne h
    · exact hA hy hx (Ne.symm hne) h

/-- Transport along a rank-preserving order isomorphism. -/
def transport {Q : Type*} [PartialOrder Q] {r' : Q → ℕ} (e : P ≃o Q)
    (he : ∀ x, r' (e x) = r x) : SCD Q r' N where
  bot y := e (S.bot (e.symm y))
  bot_le y := by
    have := e.monotone (S.bot_le (e.symm y))
    simpa using this
  comparable y y' h := by
    have h' : S.bot (e.symm y) = S.bot (e.symm y') := e.injective h
    rcases S.comparable _ _ h' with h'' | h''
    · left
      simpa using e.monotone h''
    · right
      simpa using e.monotone h''
  rank_le y := by
    have h := he (e.symm y)
    rw [e.apply_symm_apply] at h
    rw [he, h]
    exact S.rank_le _
  exists_rank y k h1 h2 := by
    rw [he] at h1 h2
    obtain ⟨z, hz, hzk⟩ := S.exists_rank (e.symm y) k h1 h2
    exact ⟨e z, by simp [hz], by rw [he, hzk]⟩

/-- The bottom of the chain through `(x, t)` in `P × Fin (L+1)`. -/
def prodBot (L : ℕ) (z : P × Fin (L + 1)) : P × Fin (L + 1) :=
  (S.pick z.1 (r (S.bot z.1) + min (r z.1 - r (S.bot z.1)) (L - z.2)), 0)

theorem prodBot_spec (hr : StrictMono r) (L : ℕ) (z : P × Fin (L + 1)) :
    S.bot (S.pick z.1 (r (S.bot z.1) + min (r z.1 - r (S.bot z.1)) (L - z.2))) = S.bot z.1 ∧
      r (S.pick z.1 (r (S.bot z.1) + min (r z.1 - r (S.bot z.1)) (L - z.2))) =
        r (S.bot z.1) + min (r z.1 - r (S.bot z.1)) (L - z.2) := by
  have h1 := S.rank_le z.1
  have h2 := S.rank_bot_le hr z.1
  exact S.pick_spec (by omega) (by omega)

/-- **De Bruijn's step.** A symmetric chain decomposition of `P` induces one of `P × Fin (L+1)`:
each grid `chain × Fin (L+1)` is cut into hooks. -/
def prod (hr : StrictMono r) (L : ℕ) :
    SCD (P × Fin (L + 1)) (fun z => r z.1 + z.2) (N + L) where
  bot := S.prodBot L
  bot_le z := by
    obtain ⟨hb, hrk⟩ := S.prodBot_spec hr L z
    simp only [prodBot]
    refine Prod.mk_le_mk.2 ⟨S.le_of_rank_le hr hb ?_, Fin.zero_le _⟩
    have := S.rank_bot_le hr z.1
    omega
  comparable z w h := by
    obtain ⟨hbz, hrz⟩ := S.prodBot_spec hr L z
    obtain ⟨hbw, hrw⟩ := S.prodBot_spec hr L w
    simp only [prodBot] at h
    have h1 := congrArg Prod.fst h
    simp only at h1
    have hb : S.bot z.1 = S.bot w.1 := hbz.symm.trans (h1 ▸ hbw)
    have hrr := congrArg r h1
    have hRw : r (S.bot w.1) = r (S.bot z.1) := by rw [hb]
    rw [hrz, hrw, hRw] at hrr
    have hz1 := S.rank_bot_le hr z.1
    have hw1 := S.rank_bot_le hr w.1
    rw [hRw] at hw1
    have hzt := z.2.isLt
    have hwt := w.2.isLt
    rw [Prod.le_def, Prod.le_def, Fin.le_iff_val_le_val, Fin.le_iff_val_le_val]
    have hle : ∀ x y : P, S.bot x = S.bot y → r x ≤ r y → x ≤ y := fun x y hxy h =>
      S.le_of_rank_le hr hxy h
    by_cases hc : r z.1 ≤ r w.1
    · by_cases ht : (z.2 : ℕ) ≤ w.2
      · exact Or.inl ⟨hle _ _ hb hc, ht⟩
      · by_cases hc' : r w.1 ≤ r z.1
        · exact Or.inr ⟨hle _ _ hb.symm hc', by omega⟩
        · exfalso
          omega
    · by_cases ht : (w.2 : ℕ) ≤ z.2
      · exact Or.inr ⟨hle _ _ hb.symm (by omega), ht⟩
      · exfalso
        omega
  rank_le z := by
    obtain ⟨hb, hrk⟩ := S.prodBot_spec hr L z
    have h1 := S.rank_le z.1
    have h2 := S.rank_bot_le hr z.1
    have h3 := z.2.isLt
    simp only [prodBot, Fin.val_zero, add_zero]
    rw [hrk]
    omega
  exists_rank z k h1 h2 := by
    obtain ⟨hb, hrk⟩ := S.prodBot_spec hr L z
    simp only [prodBot, Fin.val_zero, add_zero] at h1 h2
    rw [hrk] at h1 h2
    have hz1 := S.rank_le z.1
    have hz2 := S.rank_bot_le hr z.1
    have hzt := z.2.isLt
    set R := r (S.bot z.1)
    set u := min (r z.1 - R) (L - z.2) with hu
    -- the bottom element `y₀` of the hook
    set y₀ := S.pick z.1 (R + u)
    have hy₀ := S.pick_spec (x := z.1) (k := R + u) (by omega) (by omega)
    have hpick : ∀ y : P, S.bot y = S.bot z.1 → r y = R + u → S.pick y (R + u) = y₀ := by
      intro y hy hry
      have hs := S.pick_spec (x := y) (k := R + u) (by rw [hy]; omega) (by rw [hy]; omega)
      exact S.eq_of_rank_eq hr (hs.1.trans (hy.trans hy₀.1.symm)) (hs.2.trans hy₀.2.symm)
    have key : ∀ (y : P) (s : Fin (L + 1)), S.bot y = S.bot z.1 →
        min (r y - R) (L - s) = u → r y = R + u ∨ (s : ℕ) = L - u →
        S.prodBot L (y, s) = S.prodBot L z := by
      intro y s hy hmin _
      show (S.pick y (r (S.bot y) + min (r y - r (S.bot y)) (L - s)), (0 : Fin (L + 1))) =
        (S.pick z.1 (R + u), 0)
      rw [hy, hmin]
      congr 1
      have hs := S.pick_spec (x := y) (k := R + u) (by rw [hy]; omega)
        (by rw [hy]; have := S.rank_le y; omega)
      exact S.eq_of_rank_eq hr (hs.1.trans (hy.trans hy₀.1.symm)) (hs.2.trans hy₀.2.symm)
    by_cases hk : k ≤ R + L
    · -- vertical arm: `(y₀, k - R - u)`
      refine ⟨(y₀, ⟨k - R - u, by omega⟩), ?_, ?_⟩
      · apply key y₀ _ (hy₀.1) _ (Or.inl hy₀.2)
        simp only
        rw [hy₀.2]
        omega
      · simp only
        rw [hy₀.2]
        omega
    · -- horizontal arm: `(y, L - u)` with `r y = k - L + u`
      obtain ⟨y, hy, hry⟩ := S.exists_rank z.1 (k - L + u) (by omega) (by omega)
      refine ⟨(y, ⟨L - u, by omega⟩), ?_, ?_⟩
      · apply key y _ hy _ (Or.inr rfl)
        simp only
        rw [hry]
        omega
      · simp only
        rw [hry]
        omega

/-- The trivial decomposition of a one-point poset. -/
def unique [Subsingleton P] (hr : ∀ x, r x = 0) : SCD P r 0 where
  bot := id
  bot_le _ := le_rfl
  comparable x y _ := Or.inl (Subsingleton.elim x y ▸ le_rfl)
  rank_le x := by simp [hr]
  exists_rank x k h1 h2 := ⟨x, rfl, by simp [hr] at h2 ⊢; omega⟩

end SCD

/-! ### Divisor lattices -/

theorem rank_decomp {p m L : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m ≠ 0)
    (x : Div m × Fin (L + 1)) :
    Div.rank ((decomp hp hpm hm) x) = Div.rank x.1 + x.2 := by
  show ArithmeticFunction.cardFactors (x.1.1 * p ^ (x.2 : ℕ)) = _
  rw [ArithmeticFunction.cardFactors_mul (Div.val_ne_zero x.1) (pow_ne_zero _ hp.ne_zero),
    ArithmeticFunction.cardFactors_pow, ArithmeticFunction.cardFactors_apply_prime hp, mul_one]
  rfl

theorem rank_divCongr {N N' : ℕ} (h : N = N') (x : Div N) :
    Div.rank (divCongr h x) = Div.rank x := by
  subst h
  rfl

instance : Subsingleton (Div 1) :=
  ⟨fun a b => Subtype.ext ((Nat.dvd_one.1 (Div.val_dvd a)).trans (Nat.dvd_one.1 (Div.val_dvd b)).symm)⟩

/-- **De Bruijn–van Ebbenhorst Tengbergen–Kruyswijk.** Every divisor lattice `D(n)`, `n ≠ 0`,
has a symmetric chain decomposition with respect to `Ω`. -/
theorem nonempty_scd : ∀ n : ℕ, n ≠ 0 →
    Nonempty (SCD (Div n) Div.rank (ArithmeticFunction.cardFactors n)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h1 : n = 1
    · subst h1
      rw [ArithmeticFunction.cardFactors_one]
      exact ⟨SCD.unique (P := Div 1) (r := Div.rank) (fun x => by
          have : x.1 = 1 := Nat.dvd_one.1 (Div.val_dvd x)
          simp [Div.rank, this])⟩
    · set p := n.minFac
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
      obtain ⟨S⟩ := ih m hmn hm
      have S' := S.prod Div.rank_strictMono L
      have hΩ : ArithmeticFunction.cardFactors m + L = ArithmeticFunction.cardFactors n := by
        rw [hn', ArithmeticFunction.cardFactors_mul (pow_ne_zero _ hp.ne_zero) hm,
          ArithmeticFunction.cardFactors_pow, ArithmeticFunction.cardFactors_apply_prime hp]
        ring
      have T := S'.transport (r' := Div.rank) ((decomp (L := L) hp hpm hm).trans (divCongr hn'.symm))
        (fun x => by
          rw [OrderIso.trans_apply, rank_divCongr, rank_decomp])
      exact ⟨hΩ ▸ T⟩

/-- The middle rank of `D(n)`. -/
def midRank (n : ℕ) : Finset (Div n) :=
  univ.filter fun d : Div n => Div.rank d = ArithmeticFunction.cardFactors n / 2

theorem isAntichain_midRank (n : ℕ) : IsAntichain (· ≤ ·) (midRank n : Set (Div n)) := by
  intro x hx y hy hxy hle
  simp only [midRank, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx hy
  have := Div.rank_strictMono (lt_of_le_of_ne hle hxy)
  omega

/-- **Sperner property of divisor lattices.** Every antichain of `D(n)` has at most as many
elements as the middle rank `{d ∣ n : Ω(d) = ⌊Ω(n)/2⌋}`, which is itself an antichain. Hence
the width of `D(n)` is the size of its middle rank. -/
theorem card_le_midRank {n : ℕ} (hn : n ≠ 0) (A : Finset (Div n))
    (hA : IsAntichain (· ≤ ·) (A : Set (Div n))) : A.card ≤ (midRank n).card := by
  obtain ⟨S⟩ := nonempty_scd n hn
  exact S.card_le_mid Div.rank_strictMono A hA

/-- The middle rank is a maximum antichain. -/
theorem isMaxAntichain_midRank {n : ℕ} (hn : n ≠ 0) : IsMaxAntichain (midRank n) :=
  ⟨isAntichain_midRank n, fun t ht => card_le_midRank hn t ht⟩

end DivisorAntichains
