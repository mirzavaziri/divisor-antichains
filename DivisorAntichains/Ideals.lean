/-
Antitone maps, lower sets and antichains (blueprint, Theorem 3.2, steps 2 and 3).

For a finite poset `P`, antitone maps `P → Fin (t+1)` correspond to lower sets of `P × Fin t`,
and lower sets correspond to antichains. Combined with `D(m) × Fin t ≃o D(r^(t-1) m)` this
shows that the number of maximum antichains of `D(p^L m)` equals the number of all antichains
of `D(r^(L-Ω(m)-1) m)` (OEIS A096826 versus A096827).
-/
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Preorder.Finite
import Mathlib.Order.UpperLower.Basic
import DivisorAntichains.Groups

open Finset

noncomputable section

open Classical

namespace DivisorAntichains

section LowerAntichain

variable {β : Type*} [PartialOrder β] [Fintype β]

/-- The lower closure of a finset. -/
def lowerClos (A : Finset β) : Finset β := univ.filter fun x => ∃ a ∈ A, x ≤ a

/-- The maximal elements of a finset. -/
def maxElts (I : Finset β) : Finset β := I.filter fun x => ∀ y ∈ I, x ≤ y → y ≤ x

theorem isLowerSet_lowerClos (A : Finset β) : IsLowerSet (lowerClos A : Set β) := by
  intro x y hyx hx
  simp only [lowerClos, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
  obtain ⟨a, ha, hxa⟩ := hx
  exact ⟨a, ha, hyx.trans hxa⟩

theorem isAntichain_maxElts (I : Finset β) : IsAntichain (· ≤ ·) (maxElts I : Set β) := by
  intro a ha b hb hab hle
  simp only [maxElts, coe_filter, Set.mem_ofPred_eq] at ha hb
  exact hab (le_antisymm hle (ha.2 b hb.1 hle))

theorem maxElts_lowerClos {A : Finset β} (hA : IsAntichain (· ≤ ·) (A : Set β)) :
    maxElts (lowerClos A) = A := by
  ext x
  simp only [maxElts, lowerClos, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨⟨a, ha, hxa⟩, hmax⟩
    have hax : a ≤ x := hmax a ⟨a, ha, le_rfl⟩ hxa
    rwa [le_antisymm hxa hax]
  · intro hx
    refine ⟨⟨x, hx, le_rfl⟩, fun y ⟨a, ha, hya⟩ hxy => ?_⟩
    have hxa : x ≤ a := hxy.trans hya
    by_cases h : x = a
    · subst h
      exact hya
    · exact absurd hxa (hA hx ha h)

theorem lowerClos_maxElts {I : Finset β} (hI : IsLowerSet (I : Set β)) :
    lowerClos (maxElts I) = I := by
  ext x
  simp only [maxElts, lowerClos, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨a, ⟨haI, -⟩, hxa⟩
    exact hI hxa haI
  · intro hx
    obtain ⟨b, hxb, hbI, hbmax⟩ := Finset.exists_le_maximal I hx
    exact ⟨b, ⟨hbI, fun y hy hby => hbmax hy hby⟩, hxb⟩

/-- Antichains of a finite poset correspond to its lower sets. -/
def antichainLowerEquiv :
    {A : Finset β // IsAntichain (· ≤ ·) (A : Set β)} ≃ {I : Finset β // IsLowerSet (I : Set β)} where
  toFun A := ⟨lowerClos A.1, isLowerSet_lowerClos A.1⟩
  invFun I := ⟨maxElts I.1, isAntichain_maxElts I.1⟩
  left_inv A := Subtype.ext (maxElts_lowerClos A.2)
  right_inv I := Subtype.ext (lowerClos_maxElts I.2)

end LowerAntichain

section AntitoneLower

variable {P : Type*} [PartialOrder P] [Fintype P] {t : ℕ}

/-- The fiber of a finset of `P × Fin t` over `x`. -/
def fiber (I : Finset (P × Fin t)) (x : P) : Finset (Fin t) := univ.filter fun j => (x, j) ∈ I

omit [Fintype P] in
theorem mem_iff_lt_card_fiber {I : Finset (P × Fin t)} (hI : IsLowerSet (I : Set (P × Fin t)))
    (x : P) (j : Fin t) : (x, j) ∈ I ↔ (j : ℕ) < (fiber I x).card := by
  constructor
  · intro hj
    have hsub : Finset.Iic j ⊆ fiber I x := by
      intro i hi
      simp only [fiber, mem_filter, mem_univ, true_and]
      exact hI (Prod.mk_le_mk.2 ⟨le_rfl, Finset.mem_Iic.1 hi⟩) hj
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro hj
    by_contra hnot
    have hsub : fiber I x ⊆ Finset.Iio j := by
      intro i hi
      simp only [fiber, mem_filter, mem_univ, true_and] at hi
      rw [Finset.mem_Iio]
      by_contra hji
      exact hnot (hI (Prod.mk_le_mk.2 ⟨le_rfl, not_lt.1 hji⟩) hi)
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

/-- The lower set below the graph of an antitone map. -/
def toLower (v : P → Fin (t + 1)) : Finset (P × Fin t) :=
  univ.filter fun x => (x.2 : ℕ) < v x.1

theorem isLowerSet_toLower {v : P → Fin (t + 1)} (hv : Antitone v) :
    IsLowerSet (toLower v : Set (P × Fin t)) := by
  intro x y hyx hx
  simp only [toLower, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
  have h1 : (y.2 : ℕ) ≤ x.2 := (Prod.mk_le_mk.1 hyx).2
  have h2 : (v x.1 : ℕ) ≤ v y.1 := hv (Prod.mk_le_mk.1 hyx).1
  omega

/-- The antitone map recording the fiber sizes of a lower set. -/
def ofLower (I : Finset (P × Fin t)) : P → Fin (t + 1) := fun x =>
  ⟨(fiber I x).card, by
    have := Finset.card_le_univ (fiber I x)
    rw [Fintype.card_fin] at this
    omega⟩

omit [Fintype P] in
theorem antitone_ofLower {I : Finset (P × Fin t)} (hI : IsLowerSet (I : Set (P × Fin t))) :
    Antitone (ofLower I) := by
  intro x y hxy
  rw [Fin.le_iff_val_le_val]
  show (fiber I y).card ≤ (fiber I x).card
  apply Finset.card_le_card
  intro j hj
  simp only [fiber, mem_filter, mem_univ, true_and] at hj ⊢
  exact hI (Prod.mk_le_mk.2 ⟨hxy, le_rfl⟩) hj

theorem toLower_ofLower {I : Finset (P × Fin t)} (hI : IsLowerSet (I : Set (P × Fin t))) :
    toLower (ofLower I) = I := by
  ext ⟨x, j⟩
  simp only [toLower, mem_filter, mem_univ, true_and]
  exact (mem_iff_lt_card_fiber hI x j).symm

theorem ofLower_toLower {v : P → Fin (t + 1)} (hv : Antitone v) : ofLower (toLower v) = v := by
  funext x
  apply Fin.ext
  have hI := isLowerSet_toLower hv
  have key : ∀ j : Fin t, (j : ℕ) < (fiber (toLower v) x).card ↔ (j : ℕ) < v x := by
    intro j
    rw [← mem_iff_lt_card_fiber hI x j]
    simp [toLower]
  show (fiber (toLower v) x).card = (v x : ℕ)
  have hc : (fiber (toLower v) x).card ≤ t := by
    have := Finset.card_le_univ (fiber (toLower v) x)
    rwa [Fintype.card_fin] at this
  have hv' : (v x : ℕ) ≤ t := Nat.lt_succ_iff.1 (v x).isLt
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact absurd ((key ⟨_, lt_of_lt_of_le h hv'⟩).2 h) (lt_irrefl _)
  · exact absurd ((key ⟨_, lt_of_lt_of_le h hc⟩).1 h) (lt_irrefl _)

/-- Antitone maps `P → Fin (t+1)` correspond to lower sets of `P × Fin t`. -/
def antitoneLowerEquiv :
    {v : P → Fin (t + 1) // Antitone v} ≃
      {I : Finset (P × Fin t) // IsLowerSet (I : Set (P × Fin t))} where
  toFun v := ⟨toLower v.1, isLowerSet_toLower v.2⟩
  invFun I := ⟨ofLower I.1, antitone_ofLower I.2⟩
  left_inv v := Subtype.ext (ofLower_toLower v.2)
  right_inv I := Subtype.ext (toLower_ofLower I.2)

end AntitoneLower

/-- Antichains correspond under an order isomorphism. -/
def mapAntichainEquiv {β γ : Type*} [PartialOrder β] [PartialOrder γ] (e : β ≃o γ) :
    {s : Finset β // IsAntichain (· ≤ ·) (s : Set β)} ≃
      {s : Finset γ // IsAntichain (· ≤ ·) (s : Set γ)} where
  toFun s := ⟨s.1.map e.toEquiv.toEmbedding, (isAntichain_map_iff e s.1).2 s.2⟩
  invFun t := ⟨t.1.map e.symm.toEquiv.toEmbedding,
    (isAntichain_map_iff e _).1 (by rw [map_map_symm]; exact t.2)⟩
  left_inv s := Subtype.ext (map_symm_map e s.1)
  right_inv t := Subtype.ext (map_map_symm e t.1)

/-- `numAntichains n`: the number of antichains (including the empty one) of the divisor lattice
of `n` (OEIS A096827). -/
def numAntichains (n : ℕ) : ℕ :=
  Fintype.card {A : Finset (Div n) // IsAntichain (· ≤ ·) (A : Set (Div n))}

variable {p m L r : ℕ}

/-- **The bridge A096826 ↔ A096827.** If `p` and `r` are primes not dividing `m ≠ 0` and
`Ω(m) < L`, then the number of maximum antichains of `D(p^L m)` equals the number of antichains
of `D(r^(L - Ω(m) - 1) m)`. -/
theorem a_eq_numAntichains (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m ≠ 0) (hr : r.Prime)
    (hrm : ¬ r ∣ m) (hL : ArithmeticFunction.cardFactors m < L) :
    a (p ^ L * m) = numAntichains (r ^ (L - ArithmeticFunction.cardFactors m - 1) * m) := by
  rw [a_eq_card hp hpm hm hL.le, numAntichains]
  obtain ⟨s, hs⟩ : ∃ s, L - ArithmeticFunction.cardFactors m = s + 1 :=
    ⟨L - ArithmeticFunction.cardFactors m - 1, by omega⟩
  have hs' : L - ArithmeticFunction.cardFactors m - 1 = s := by omega
  rw [hs', Fintype.card_congr (antitoneLowerEquiv (P := Div m) (t := L - ArithmeticFunction.cardFactors m))]
  rw [← Fintype.card_congr (antichainLowerEquiv (β := Div m × Fin (L - ArithmeticFunction.cardFactors m)))]
  rw [hs]
  exact Fintype.card_congr (mapAntichainEquiv (decomp (L := s) hr hrm hm))

/-- **Dedekind-number case.** If `p` is a prime not dividing `m ≠ 0`, then
`a(p^(Ω(m)+1) m)` equals the number of antichains of `D(m)`. For squarefree `m` with `k` prime
factors, `D(m)` is the Boolean lattice on `k` atoms, so this is the Dedekind number `M(k)`. -/
theorem a_pow_succ_eq_numAntichains (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m ≠ 0) :
    a (p ^ (ArithmeticFunction.cardFactors m + 1) * m) = numAntichains m := by
  obtain ⟨r, hrm, hr⟩ := Nat.exists_infinite_primes (m + 1)
  have hrdvd : ¬ r ∣ m := fun h => by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) h
    omega
  rw [a_eq_numAntichains hp hpm hm hr hrdvd (by omega)]
  congr 1
  simp

end DivisorAntichains
