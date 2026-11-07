/-
The divisor lattice `D(n)` as a finite poset, its rank function `Ω`, and the decomposition
`D(p^L * m) ≃o D(m) × Fin (L+1)` for a prime `p` not dividing `m`
(blueprint, Section 1 and Proposition 2.3).
-/
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Hom.Basic
import DivisorAntichains.Fibers
import DivisorAntichains.RankShift

open Finset

namespace DivisorAntichains

/-- The divisors of `n`, as a type that will be ordered by divisibility. -/
def Div (n : ℕ) : Type := {d : ℕ // d ∈ n.divisors}

namespace Div

variable {n : ℕ}

instance : Fintype (Div n) := inferInstanceAs (Fintype {d : ℕ // d ∈ n.divisors})
instance : DecidableEq (Div n) := inferInstanceAs (DecidableEq {d : ℕ // d ∈ n.divisors})

/-- Divisibility order on the divisors of `n`. -/
instance : PartialOrder (Div n) where
  le a b := a.1 ∣ b.1
  le_refl a := dvd_refl a.1
  le_trans _ _ _ hab hbc := dvd_trans hab hbc
  le_antisymm a b hab hba := Subtype.ext (Nat.dvd_antisymm hab hba)

theorem le_def {a b : Div n} : a ≤ b ↔ a.1 ∣ b.1 := Iff.rfl

theorem card_eq : Fintype.card (Div n) = n.divisors.card :=
  Fintype.card_coe n.divisors

theorem val_ne_zero (a : Div n) : a.1 ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors a.2)

theorem val_dvd (a : Div n) : a.1 ∣ n := Nat.dvd_of_mem_divisors a.2

theorem ne_zero_of (a : Div n) : n ≠ 0 := (Nat.mem_divisors.1 a.2).2

instance [NeZero n] : OrderBot (Div n) where
  bot := ⟨1, Nat.mem_divisors.2 ⟨one_dvd n, NeZero.ne n⟩⟩
  bot_le a := one_dvd a.1

instance [NeZero n] : OrderTop (Div n) where
  top := ⟨n, Nat.mem_divisors.2 ⟨dvd_refl n, NeZero.ne n⟩⟩
  le_top a := Nat.dvd_of_mem_divisors a.2

@[simp] theorem bot_val [NeZero n] : (⊥ : Div n).1 = 1 := rfl
@[simp] theorem top_val [NeZero n] : (⊤ : Div n).1 = n := rfl

/-- The rank of a divisor: its number of prime factors counted with multiplicity. -/
def rank (a : Div n) : ℕ := ArithmeticFunction.cardFactors a.1

theorem rank_strictMono : StrictMono (rank : Div n → ℕ) := by
  intro a b hab
  have hne : a.1 ≠ b.1 := fun h => hab.ne (Subtype.ext h)
  obtain ⟨k, hk⟩ := (le_def.1 hab.le)
  have ha := val_ne_zero a
  have hb := val_ne_zero b
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    exact hb hk
  have hk1 : k ≠ 1 := by
    rintro rfl
    rw [mul_one] at hk
    exact hne hk.symm
  have hΩ : ArithmeticFunction.cardFactors k ≠ 0 := by
    rw [Ne, ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one]
    tauto
  unfold rank
  rw [hk, ArithmeticFunction.cardFactors_mul ha hk0]
  omega

theorem rank_cover (a b : Div n) (hab : a < b) :
    ∃ z, a < z ∧ z ≤ b ∧ rank z = rank a + 1 := by
  have hne : a.1 ≠ b.1 := fun h => hab.ne (Subtype.ext h)
  obtain ⟨k, hk⟩ := (le_def.1 hab.le)
  have ha := val_ne_zero a
  have hk1 : k ≠ 1 := by
    rintro rfl
    rw [mul_one] at hk
    exact hne hk.symm
  obtain ⟨l, hl, hlk⟩ := Nat.exists_prime_and_dvd hk1
  have hzb : a.1 * l ∣ b.1 := by
    rw [hk]
    exact mul_dvd_mul_left _ hlk
  have hz : a.1 * l ∈ n.divisors :=
    Nat.mem_divisors.2 ⟨dvd_trans hzb (val_dvd b), ne_zero_of a⟩
  refine ⟨⟨a.1 * l, hz⟩, lt_of_le_of_ne (le_def.2 (Dvd.intro l rfl)) ?_, hzb, ?_⟩
  · intro h
    have h' : a.1 * 1 = a.1 * l := by
      rw [mul_one]
      exact congrArg Subtype.val h
    have := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha) h'
    exact hl.one_lt.ne this
  · show ArithmeticFunction.cardFactors (a.1 * l) = ArithmeticFunction.cardFactors a.1 + 1
    rw [ArithmeticFunction.cardFactors_mul ha hl.ne_zero,
      ArithmeticFunction.cardFactors_apply_prime hl]

theorem rank_bot [NeZero n] : rank (⊥ : Div n) = 0 := by
  simp [rank]

theorem rank_top [NeZero n] : rank (⊤ : Div n) = ArithmeticFunction.cardFactors n := rfl

end Div

section Decomposition

variable {p m L : ℕ}

/-- If `p ∤ q` and `p ∤ q'`, then `q p^j ∣ q' p^j'` iff `q ∣ q'` and `j ≤ j'`. -/
theorem mul_pow_dvd_mul_pow_iff (hp : p.Prime) {q q' j j' : ℕ} (hq : ¬ p ∣ q) (hq' : ¬ p ∣ q')
    (hq0 : q ≠ 0) (hq0' : q' ≠ 0) :
    q * p ^ j ∣ q' * p ^ j' ↔ q ∣ q' ∧ j ≤ j' := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have hcop : Nat.Coprime q (p ^ j') :=
        Nat.Coprime.pow_right _ (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hq))
      exact hcop.dvd_of_dvd_mul_right (dvd_trans (dvd_mul_right q (p ^ j)) h)
    · have hpos : q' * p ^ j' ≠ 0 := mul_ne_zero hq0' (pow_ne_zero _ hp.ne_zero)
      have hle := (Nat.factorization_le_iff_dvd (mul_ne_zero hq0 (pow_ne_zero _ hp.ne_zero))
        hpos).2 h p
      rw [Nat.factorization_mul hq0 (pow_ne_zero _ hp.ne_zero),
        Nat.factorization_mul hq0' (pow_ne_zero _ hp.ne_zero)] at hle
      simp only [Finsupp.coe_add, Pi.add_apply, Nat.factorization_pow_self hp,
        Nat.factorization_eq_zero_of_not_dvd hq, Nat.factorization_eq_zero_of_not_dvd hq',
        zero_add] at hle
      exact hle
  · rintro ⟨h1, h2⟩
    exact mul_dvd_mul h1 (pow_dvd_pow p h2)

theorem not_dvd_of_div (hpm : ¬ p ∣ m) (q : Div m) : ¬ p ∣ q.1 :=
  fun h => hpm (dvd_trans h (Div.val_dvd q))

/-- The map `(q, j) ↦ q p^j`. -/
def decompFun (hp : p.Prime) (hm : m ≠ 0) (x : Div m × Fin (L + 1)) : Div (p ^ L * m) :=
  ⟨x.1.1 * p ^ (x.2 : ℕ), Nat.mem_divisors.2
    ⟨by
      rw [mul_comm (p ^ L)]
      exact mul_dvd_mul (Div.val_dvd x.1) (pow_dvd_pow p (Nat.lt_succ_iff.1 x.2.isLt)),
     mul_ne_zero (pow_ne_zero _ hp.ne_zero) hm⟩⟩

theorem decompFun_le_iff (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m ≠ 0)
    (x y : Div m × Fin (L + 1)) :
    decompFun hp hm x ≤ decompFun hp hm y ↔ x ≤ y := by
  rw [Div.le_def, Prod.le_def, Div.le_def, Fin.le_iff_val_le_val]
  exact mul_pow_dvd_mul_pow_iff hp (not_dvd_of_div hpm x.1) (not_dvd_of_div hpm y.1)
    (Div.val_ne_zero x.1) (Div.val_ne_zero y.1)

theorem decompFun_surjective (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m ≠ 0) :
    Function.Surjective (decompFun (L := L) hp hm) := by
  intro d
  have hd0 := Div.val_ne_zero d
  have hn0 : p ^ L * m ≠ 0 := mul_ne_zero (pow_ne_zero _ hp.ne_zero) hm
  have hfac : (p ^ L * m).factorization p = L := by
    rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm]
    simp [Nat.Prime.factorization_self hp, Nat.factorization_eq_zero_of_not_dvd hpm]
  have hjL : d.1.factorization p ≤ L := by
    have := (Nat.factorization_le_iff_dvd hd0 hn0).2 (Div.val_dvd d) p
    rwa [hfac] at this
  have hcompl : (p ^ L * m) / p ^ (p ^ L * m).factorization p = m := by
    rw [hfac, Nat.mul_div_cancel_left _ (pow_pos hp.pos _)]
  have hq : d.1 / p ^ d.1.factorization p ∣ m := by
    have := Nat.ordCompl_dvd_ordCompl_of_dvd (Div.val_dvd d) p
    rwa [hcompl] at this
  refine ⟨(⟨d.1 / p ^ d.1.factorization p, Nat.mem_divisors.2 ⟨hq, hm⟩⟩,
    ⟨d.1.factorization p, Nat.lt_succ_of_le hjL⟩), ?_⟩
  apply Subtype.ext
  show d.1 / p ^ d.1.factorization p * p ^ d.1.factorization p = d.1
  rw [mul_comm]
  exact Nat.ordProj_mul_ordCompl_eq_self d.1 p

/-- The decomposition `D(m) × Fin (L+1) ≃o D(p^L m)` for a prime `p` not dividing `m`. -/
noncomputable def decomp (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m ≠ 0) :
    Div m × Fin (L + 1) ≃o Div (p ^ L * m) :=
  OrderIso.ofSurjective
    (OrderEmbedding.ofMapLEIff (decompFun hp hm) (decompFun_le_iff hp hpm hm))
    (decompFun_surjective hp hpm hm)

end Decomposition

end DivisorAntichains
