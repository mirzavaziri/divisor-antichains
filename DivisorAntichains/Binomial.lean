/-
Two prime factors (blueprint, Corollary 3.4(a)):
`a(p^L q^s) = binomial(L+1, s+1)` for distinct primes `p, q` and `s ≤ L`.

The count reduces to antitone maps `Fin (s+1) → Fin (L-s+1)`, which correspond to strictly
monotone maps `Fin (s+1) → Fin (L+1)`, that is, to `(s+1)`-element subsets of `Fin (L+1)`.
-/
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Powerset
import Mathlib.SetTheory.Cardinal.Finite
import DivisorAntichains.Ideals

open Finset

noncomputable section

open Classical

namespace DivisorAntichains

section Counting

/-- A strictly monotone map on `Fin n` increases by at least the distance. -/
theorem StrictMono.add_sub_le {n N : ℕ} {f : Fin n → Fin N} (hf : StrictMono f) :
    ∀ d : ℕ, ∀ i j : Fin n, (j : ℕ) = i + d → (f i : ℕ) + d ≤ f j := by
  intro d
  induction d with
  | zero =>
    intro i j h
    have : i = j := Fin.ext (by omega)
    subst this
    simp
  | succ d ih =>
    intro i j h
    let j' : Fin n := ⟨i + d, by omega⟩
    have h1 := ih i j' rfl
    have h2 : f j' < f j := hf (Fin.lt_def.2 (by show (i : ℕ) + d < j; omega))
    rw [Fin.lt_def] at h2
    omega

/-- Strictly monotone maps `Fin k → Fin N` correspond to `k`-element subsets of `Fin N`. -/
def strictMonoFinsetEquiv (k N : ℕ) :
    {f : Fin k → Fin N // StrictMono f} ≃ {s : Finset (Fin N) // s.card = k} where
  toFun f := ⟨univ.image f.1, by rw [card_image_of_injective _ f.2.injective, card_univ,
    Fintype.card_fin]⟩
  invFun s := ⟨s.1.orderEmbOfFin s.2, (s.1.orderEmbOfFin s.2).strictMono⟩
  left_inv f := by
    apply Subtype.ext
    exact (orderEmbOfFin_unique _ (fun x => mem_image_of_mem _ (mem_univ x)) f.2).symm
  right_inv s := by
    apply Subtype.ext
    apply Finset.coe_injective
    rw [coe_image, coe_univ, Set.image_univ]
    exact range_orderEmbOfFin s.1 s.2

/-- Antitone maps `Fin n → Fin (k+1)` correspond to strictly monotone maps `Fin n → Fin (n+k)`,
via `v ↦ (i ↦ i + k - v i)`. -/
def antitoneStrictMonoEquiv (n k : ℕ) :
    {v : Fin n → Fin (k + 1) // Antitone v} ≃ {f : Fin n → Fin (n + k) // StrictMono f} where
  toFun v := ⟨fun i => ⟨i + (k - v.1 i), by have := i.isLt; omega⟩, fun i j hij => by
    rw [Fin.mk_lt_mk]
    have h1 : (v.1 j : ℕ) ≤ v.1 i := v.2 hij.le
    have h2 : (i : ℕ) < j := hij
    omega⟩
  invFun f := ⟨fun i => ⟨k - (f.1 i - i), by omega⟩, fun i j hij => by
    rw [Fin.mk_le_mk]
    rcases eq_or_lt_of_le hij with h | h
    · rw [h]
    · have := StrictMono.add_sub_le f.2 (j - i) i j (by have : (i : ℕ) < j := h; omega)
      omega⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    show k - (i + (k - v.1 i) - i) = v.1 i
    have := (v.1 i).isLt
    omega
  right_inv f := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    show (i : ℕ) + (k - (k - (f.1 i - i))) = f.1 i
    have hlow := StrictMono.add_sub_le f.2 i ⟨0, by have := i.isLt; omega⟩ i (by simp)
    have hn : 0 < n := by have := i.isLt; omega
    have hup := StrictMono.add_sub_le f.2 (n - 1 - i) i ⟨n - 1, by omega⟩
      (by simp; have := i.isLt; omega)
    have h3 := (f.1 ⟨n - 1, by omega⟩).isLt
    omega

/-- The number of antitone maps `Fin n → Fin (k+1)` is `binomial(n+k, n)`. -/
theorem card_antitone_fin (n k : ℕ) :
    Fintype.card {v : Fin n → Fin (k + 1) // Antitone v} = (n + k).choose n := by
  rw [Fintype.card_congr ((antitoneStrictMonoEquiv n k).trans (strictMonoFinsetEquiv n (n + k))),
    Fintype.card_finset_len, Fintype.card_fin]

/-- Antitone maps are transported along order isomorphisms of the domain. -/
def antitoneCongrEquiv {P Q X : Type*} [Preorder P] [Preorder Q] [Preorder X] (e : P ≃o Q) :
    {v : P → X // Antitone v} ≃ {v : Q → X // Antitone v} where
  toFun v := ⟨v.1 ∘ e.symm, fun x y h => v.2 (e.symm.monotone h)⟩
  invFun w := ⟨w.1 ∘ e, fun x y h => w.2 (e.monotone h)⟩
  left_inv v := by
    apply Subtype.ext
    funext x
    simp
  right_inv w := by
    apply Subtype.ext
    funext x
    simp

end Counting

section TwoPrimes

variable {p q s L : ℕ}

/-- The unique divisor of `1`. -/
def oneDiv : Div 1 := ⟨1, by simp⟩

/-- The divisor lattice of `1` is a single point, so `Fin k ≃o D(1) × Fin k`. -/
def finOrderIsoDivOne (k : ℕ) : Fin k ≃o Div 1 × Fin k :=
  OrderIso.ofSurjective
    (OrderEmbedding.ofMapLEIff (fun j => (oneDiv, j))
      (fun a b => ⟨fun h => (Prod.mk_le_mk.1 h).2, fun h => Prod.mk_le_mk.2 ⟨le_refl _, h⟩⟩))
    (by
      rintro ⟨d, j⟩
      refine ⟨j, ?_⟩
      have hd : d.1 = 1 := Nat.dvd_one.1 (Div.val_dvd d)
      exact Prod.ext (Subtype.ext hd.symm) rfl)

/-- Equal numbers have isomorphic divisor lattices. -/
def divCongr {N N' : ℕ} (h : N = N') : Div N ≃o Div N' := by
  subst h
  exact OrderIso.refl _

/-- **Two prime factors.** For distinct primes `p, q` and `s ≤ L`,
`a(p^L q^s) = binomial(L+1, s+1)`. -/
theorem a_two_primes (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hsL : s ≤ L) :
    a (p ^ L * q ^ s) = (L + 1).choose (s + 1) := by
  have hpm : ¬ p ∣ q ^ s := fun h =>
    hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow h))
  have hm : q ^ s ≠ 0 := pow_ne_zero _ hq.ne_zero
  have hΩ : ArithmeticFunction.cardFactors (q ^ s) = s := by
    rw [ArithmeticFunction.cardFactors_pow, ArithmeticFunction.cardFactors_apply_prime hq,
      mul_one]
  have h1 := a_eq_card (L := L) hp hpm hm (by rw [hΩ]; exact hsL)
  rw [hΩ] at h1
  let E : Fin (s + 1) ≃o Div (q ^ s) :=
    ((finOrderIsoDivOne (s + 1)).trans (decomp (L := s) hq (by simp [hq.ne_one]) one_ne_zero)).trans
      (divCongr (mul_one (q ^ s)))
  rw [h1, Fintype.card_eq_nat_card,
    ← Nat.card_congr (antitoneCongrEquiv (X := Fin (L - s + 1)) E), ← Fintype.card_eq_nat_card,
    card_antitone_fin]
  congr 1
  omega

end TwoPrimes

end DivisorAntichains
