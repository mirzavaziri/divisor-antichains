/-
Main counting theorem in the dominated case (blueprint, Theorems 3.1 and 3.2):

if `p` is a prime not dividing `m ≠ 0` and `Ω(m) ≤ L`, then the maximum antichains of the
divisor lattice of `p^L * m` are counted by the antitone maps `D(m) → Fin (L - Ω(m) + 1)`,
and the width of that lattice is the number of divisors of `m`.
-/
import DivisorAntichains.Divisors

open Finset

namespace DivisorAntichains

section Transfer

variable {β γ : Type*} [PartialOrder β] [PartialOrder γ]

theorem isAntichain_map_iff (e : β ≃o γ) (s : Finset β) :
    IsAntichain (· ≤ ·) ((s.map e.toEquiv.toEmbedding : Finset γ) : Set γ) ↔
      IsAntichain (· ≤ ·) (s : Set β) := by
  constructor
  · intro h a ha b hb hab hle
    apply h (Finset.mem_map_of_mem _ ha) (Finset.mem_map_of_mem _ hb)
    · intro e'
      exact hab (e.injective e')
    · exact e.le_iff_le.2 hle
  · intro h x hx y hy hxy hle
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 hy
    apply h ha hb
    · intro e'
      exact hxy (by rw [e'])
    · exact e.le_iff_le.1 hle

theorem map_symm_map (e : β ≃o γ) (s : Finset β) :
    (s.map e.toEquiv.toEmbedding).map e.symm.toEquiv.toEmbedding = s := by
  ext a
  simp

theorem map_map_symm (e : β ≃o γ) (t : Finset γ) :
    (t.map e.symm.toEquiv.toEmbedding).map e.toEquiv.toEmbedding = t := by
  ext a
  simp

theorem isMaxAntichain_map_iff (e : β ≃o γ) (s : Finset β) :
    IsMaxAntichain (s.map e.toEquiv.toEmbedding) ↔ IsMaxAntichain s := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(isAntichain_map_iff e s).1 h1, fun t ht => ?_⟩
    have := h2 (t.map e.toEquiv.toEmbedding) ((isAntichain_map_iff e t).2 ht)
    simpa [Finset.card_map] using this
  · rintro ⟨h1, h2⟩
    refine ⟨(isAntichain_map_iff e s).2 h1, fun t ht => ?_⟩
    have ht' : IsAntichain (· ≤ ·) ((t.map e.symm.toEquiv.toEmbedding : Finset β) : Set β) :=
      (isAntichain_map_iff e _).1 (by rw [map_map_symm]; exact ht)
    have := h2 _ ht'
    simpa [Finset.card_map] using this

open Classical in
/-- The number of maximum antichains is an order invariant. -/
theorem card_maxAntichains_congr [Fintype β] [Fintype γ] (e : β ≃o γ) :
    (univ.filter fun s : Finset β => IsMaxAntichain s).card =
      (univ.filter fun s : Finset γ => IsMaxAntichain s).card := by
  refine Finset.card_bij' (fun s _ => s.map e.toEquiv.toEmbedding)
    (fun t _ => t.map e.symm.toEquiv.toEmbedding) ?_ ?_ ?_ ?_
  · intro s hs
    exact mem_filter.2 ⟨mem_univ _, (isMaxAntichain_map_iff e s).2 (mem_filter.1 hs).2⟩
  · intro t ht
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    exact (isMaxAntichain_map_iff e _).1 (by rw [map_map_symm]; exact (mem_filter.1 ht).2)
  · intro s _
    exact map_symm_map e s
  · intro t _
    exact map_map_symm e t

end Transfer

open Classical in
/-- `a n`: the number of maximum antichains of the divisor lattice of `n` (OEIS A096826). -/
noncomputable def a (n : ℕ) : ℕ :=
  (univ.filter fun s : Finset (Div n) => IsMaxAntichain s).card

section Dominated

variable {p m L : ℕ}

/-- A strictly antitone map `D(m) → Fin (L+1)` exists as soon as `Ω(m) ≤ L`. -/
theorem exists_strictAnti (hm : m ≠ 0) (hL : ArithmeticFunction.cardFactors m ≤ L) :
    ∃ c : Div m → Fin (L + 1), StrictAnti c := by
  have : NeZero m := ⟨hm⟩
  have hle : ∀ x : Div m, Div.rank x ≤ ArithmeticFunction.cardFactors m := fun x =>
    Div.rank_top (n := m) ▸ Div.rank_strictMono.monotone le_top
  refine ⟨fun x => ⟨ArithmeticFunction.cardFactors m - Div.rank x, by omega⟩, ?_⟩
  intro x y hxy
  show (⟨_, _⟩ : Fin (L + 1)) < ⟨_, _⟩
  rw [Fin.mk_lt_mk]
  have h1 := Div.rank_strictMono hxy
  have h2 := hle y
  omega

open Classical in
/-- **Main theorem (dominated case).** If `p` is prime, `p ∤ m`, `m ≠ 0` and `Ω(m) ≤ L`, then
the number of maximum antichains of `D(p^L m)` equals the number of antitone maps
`D(m) → Fin (L - Ω(m) + 1)`. -/
theorem a_dominated (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m ≠ 0)
    (hL : ArithmeticFunction.cardFactors m ≤ L) :
    a (p ^ L * m) =
      (univ.filter fun v : Div m → Fin (L - ArithmeticFunction.cardFactors m + 1) =>
        Antitone v).card := by
  have : NeZero m := ⟨hm⟩
  obtain ⟨c₀, hc₀⟩ := exists_strictAnti hm hL
  unfold a
  rw [← card_maxAntichains_congr (decomp (L := L) hp hpm hm), card_maxAntichains hc₀]
  convert card_strictAnti_eq_card_antitone (α := Div m) Div.rank Div.rank_strictMono
    Div.rank_cover (Div.rank_bot (n := m)) (Nat.add_sub_of_le hL).symm

/-- **Width in the dominated case.** Every antichain of `D(p^L m)` has at most `d(m)` elements,
and some antichain has exactly `d(m)` elements. -/
theorem width_dominated (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m ≠ 0)
    (hL : ArithmeticFunction.cardFactors m ≤ L) :
    (∀ t : Finset (Div (p ^ L * m)),
      IsAntichain (· ≤ ·) (t : Set (Div (p ^ L * m))) → t.card ≤ m.divisors.card) ∧
    ∃ s : Finset (Div (p ^ L * m)), IsAntichain (· ≤ ·) (s : Set (Div (p ^ L * m))) ∧
      s.card = m.divisors.card := by
  classical
  obtain ⟨c₀, hc₀⟩ := exists_strictAnti hm hL
  obtain ⟨h1, s, hs, hcard⟩ := width_eq hc₀
  set e := decomp (L := L) hp hpm hm
  refine ⟨fun t ht => ?_, s.map e.toEquiv.toEmbedding, (isAntichain_map_iff e s).2 hs, ?_⟩
  · have ht' : IsAntichain (· ≤ ·)
        ((t.map e.symm.toEquiv.toEmbedding : Finset (Div m × Fin (L + 1))) :
          Set (Div m × Fin (L + 1))) :=
      (isAntichain_map_iff e _).1 (by rw [map_map_symm]; exact ht)
    have := h1 _ ht'
    rw [Finset.card_map, Div.card_eq] at this
    exact this
  · rw [Finset.card_map, hcard, Div.card_eq]

end Dominated

section Equivalence

variable {p m L : ℕ}

/-- Maximum antichains correspond under an order isomorphism. -/
def mapMaxEquiv {β γ : Type*} [PartialOrder β] [PartialOrder γ] (e : β ≃o γ) :
    {s : Finset β // IsMaxAntichain s} ≃ {s : Finset γ // IsMaxAntichain s} where
  toFun s := ⟨s.1.map e.toEquiv.toEmbedding, (isMaxAntichain_map_iff e s.1).2 s.2⟩
  invFun t := ⟨t.1.map e.symm.toEquiv.toEmbedding,
    (isMaxAntichain_map_iff e _).1 (by rw [map_map_symm]; exact t.2)⟩
  left_inv s := Subtype.ext (map_symm_map e s.1)
  right_inv t := Subtype.ext (map_map_symm e t.1)

theorem L_eq_rank_top [NeZero m] (hL : ArithmeticFunction.cardFactors m ≤ L) :
    L = Div.rank (⊤ : Div m) + (L - ArithmeticFunction.cardFactors m) := by
  rw [Div.rank_top]
  omega

/-- **The explicit bijection (dominated case).** Antitone maps `D(m) → Fin (L - Ω(m) + 1)`
correspond to maximum antichains of `D(p^L m)`: the map `v` is sent to the set of divisors
`q * p ^ (v q + Ω(m) - Ω(q))`, `q ∣ m`. -/
noncomputable def maxAntichainEquiv (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m ≠ 0) [NeZero m]
    (hL : ArithmeticFunction.cardFactors m ≤ L) :
    {v : Div m → Fin (L - ArithmeticFunction.cardFactors m + 1) // Antitone v} ≃
      {s : Finset (Div (p ^ L * m)) // IsMaxAntichain s} :=
  (shiftEquiv (α := Div m) Div.rank Div.rank_strictMono Div.rank_cover (Div.rank_bot (n := m))
      (L_eq_rank_top hL)).symm.trans
    ((graphEquiv (exists_strictAnti hm hL).choose_spec).trans (mapMaxEquiv (decomp hp hpm hm)))

theorem maxAntichainEquiv_apply (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m ≠ 0) [NeZero m]
    (hL : ArithmeticFunction.cardFactors m ≤ L)
    (v : {v : Div m → Fin (L - ArithmeticFunction.cardFactors m + 1) // Antitone v}) :
    (maxAntichainEquiv hp hpm hm hL v).1 =
      (graph (shiftUp Div.rank (L_eq_rank_top hL) v.1)).map
        (decomp hp hpm hm).toEquiv.toEmbedding := rfl

end Equivalence

end DivisorAntichains
