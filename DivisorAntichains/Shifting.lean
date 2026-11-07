/-
The shifting argument (blueprint, Theorem 2.4, reduction step).

In a finite ranked poset with the Sperner property, suppose that the upper shadow of every
nonempty set strictly below the middle is strictly larger than the set (and dually above the
middle), and that in the odd case the same holds for proper subsets of the lower middle rank.
Then every maximum antichain is one of the middle ranks. The proof replaces the lowest (or
highest) rank of an antichain by its shadow, which would produce a larger antichain.
-/
import DivisorAntichains.SymmetricChains

open Finset

noncomputable section

open Classical

namespace DivisorAntichains

section Shifting

variable {P : Type*} [PartialOrder P] [Fintype P] (r : P → ℕ)

/-- The elements of rank `k`. -/
def level (k : ℕ) : Finset P := univ.filter fun x => r x = k

/-- The upper shadow of `S` at rank `k + 1`. -/
def up (S : Finset P) (k : ℕ) : Finset P := (level r (k + 1)).filter fun y => ∃ x ∈ S, x ≤ y

/-- The lower shadow of `S` at rank `k - 1`. -/
def down (S : Finset P) (k : ℕ) : Finset P := (level r (k - 1)).filter fun y => ∃ x ∈ S, y ≤ x

variable {r}

omit [PartialOrder P] in
theorem mem_level {k : ℕ} {x : P} : x ∈ level r k ↔ r x = k := by simp [level]

theorem mem_up {S : Finset P} {k : ℕ} {y : P} :
    y ∈ up r S k ↔ r y = k + 1 ∧ ∃ x ∈ S, x ≤ y := by
  simp [up, level]

theorem mem_down {S : Finset P} {k : ℕ} {y : P} :
    y ∈ down r S k ↔ r y = k - 1 ∧ ∃ x ∈ S, y ≤ x := by
  simp [down, level]

theorem isAntichain_level (hr : StrictMono r) (k : ℕ) :
    IsAntichain (· ≤ ·) (level r k : Set P) := by
  intro x hx y hy hxy hle
  rw [mem_coe, mem_level] at hx hy
  have := hr (lt_of_le_of_ne hle hxy)
  omega

omit [Fintype P] in
theorem eq_of_le_of_rank_le (hr : StrictMono r) {x y : P} (hle : x ≤ y) (hr' : r y ≤ r x) :
    x = y := by
  by_contra hne
  have := hr (lt_of_le_of_ne hle hne)
  omega

/-- Shifting the lowest rank `k` of an antichain up to its shadow keeps an antichain, and the
shadow is disjoint from the rest. -/
theorem shift_up (hr : StrictMono r) {A : Finset P} (hA : IsAntichain (· ≤ ·) (A : Set P))
    {k : ℕ} (hmin : ∀ x ∈ A, k ≤ r x) :
    IsAntichain (· ≤ ·)
        ((A.filter (fun x => r x ≠ k) ∪ up r (A.filter (fun x => r x = k)) k : Finset P) : Set P) ∧
      Disjoint (A.filter (fun x => r x ≠ k)) (up r (A.filter (fun x => r x = k)) k) := by
  have hup : ∀ y ∈ up r (A.filter (fun x => r x = k)) k, r y = k + 1 ∧
      ∃ x ∈ A, r x = k ∧ x ≤ y := by
    intro y hy
    simp only [up, mem_filter, mem_level] at hy
    obtain ⟨hy1, x, hx, hxy⟩ := hy
    exact ⟨hy1, x, hx.1, hx.2, hxy⟩
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab hle
    rw [mem_coe, mem_union] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hA (mem_filter.1 ha).1 (mem_filter.1 hb).1 hab hle
    · obtain ⟨hb1, x, hx, hxk, hxb⟩ := hup b hb
      have h1 := hmin a (mem_filter.1 ha).1
      have h2 := (mem_filter.1 ha).2
      exact hab (eq_of_le_of_rank_le hr hle (by omega))
    · obtain ⟨ha1, x, hx, hxk, hxa⟩ := hup a ha
      have hb2 := (mem_filter.1 hb).2
      have hxb : x ≠ b := fun e => hb2 (e ▸ hxk)
      exact hA hx (mem_filter.1 hb).1 hxb (hxa.trans hle)
    · obtain ⟨ha1, -⟩ := hup a ha
      obtain ⟨hb1, -⟩ := hup b hb
      exact hab (eq_of_le_of_rank_le hr hle (by omega))
  · rw [Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨hy1, x, hx, hxk, hxy⟩ := hup y hy'
    have hne : x ≠ y := fun e => (mem_filter.1 hy).2 (e ▸ hxk)
    exact hA hx (mem_filter.1 hy).1 hne hxy

/-- Shifting the highest rank `k` of an antichain down to its shadow. -/
theorem shift_down (hr : StrictMono r) {A : Finset P} (hA : IsAntichain (· ≤ ·) (A : Set P))
    {k : ℕ} (hk : 0 < k) (hmax : ∀ x ∈ A, r x ≤ k) :
    IsAntichain (· ≤ ·)
        ((A.filter (fun x => r x ≠ k) ∪ down r (A.filter (fun x => r x = k)) k : Finset P) :
          Set P) ∧
      Disjoint (A.filter (fun x => r x ≠ k)) (down r (A.filter (fun x => r x = k)) k) := by
  have hdn : ∀ y ∈ down r (A.filter (fun x => r x = k)) k, r y = k - 1 ∧
      ∃ x ∈ A, r x = k ∧ y ≤ x := by
    intro y hy
    simp only [down, mem_filter, mem_level] at hy
    obtain ⟨hy1, x, hx, hxy⟩ := hy
    exact ⟨hy1, x, hx.1, hx.2, hxy⟩
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab hle
    rw [mem_coe, mem_union] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hA (mem_filter.1 ha).1 (mem_filter.1 hb).1 hab hle
    · obtain ⟨hb1, x, hx, hxk, hbx⟩ := hdn b hb
      have ha2 := (mem_filter.1 ha).2
      have hax : a ≠ x := fun e => ha2 (e ▸ hxk)
      exact hA (mem_filter.1 ha).1 hx hax (hle.trans hbx)
    · obtain ⟨ha1, -⟩ := hdn a ha
      have h1 := hmax b (mem_filter.1 hb).1
      have h2 := (mem_filter.1 hb).2
      exact hab (eq_of_le_of_rank_le hr hle (by omega))
    · obtain ⟨ha1, -⟩ := hdn a ha
      obtain ⟨hb1, -⟩ := hdn b hb
      exact hab (eq_of_le_of_rank_le hr hle (by omega))
  · rw [Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨hy1, x, hx, hxk, hyx⟩ := hdn y hy'
    have hne : y ≠ x := fun e => (mem_filter.1 hy).2 (e ▸ hxk)
    exact hA (mem_filter.1 hy).1 hx hne hyx

omit [PartialOrder P] [Fintype P] in
theorem card_split (A : Finset P) (k : ℕ) :
    A.card = (A.filter fun x => r x ≠ k).card + (A.filter fun x => r x = k).card := by
  rw [add_comm]
  exact (Finset.card_filter_add_card_filter_not (s := A) (fun x => r x = k)).symm

/-- **The shifting theorem.** Under the expansion hypotheses, every maximum antichain is a
middle rank. -/
theorem eq_level_of_isMaxAntichain (hr : StrictMono r) {N : ℕ}
    (hwidth : ∀ A : Finset P, IsAntichain (· ≤ ·) (A : Set P) → A.card ≤ (level r (N / 2)).card)
    (hup : ∀ k (S : Finset P), S ⊆ level r k → S.Nonempty → 2 * k + 1 < N →
      S.card < (up r S k).card)
    (hdown : ∀ k (S : Finset P), S ⊆ level r k → S.Nonempty → N + 1 < 2 * k →
      S.card < (down r S k).card)
    (hmid : N % 2 = 1 → ∀ S : Finset P, S ⊆ level r (N / 2) → S.Nonempty →
      S ≠ level r (N / 2) → S.card < (up r S (N / 2)).card)
    (hupfull : N % 2 = 1 → up r (level r (N / 2)) (N / 2) = level r (N / 2 + 1))
    (hsym : N % 2 = 1 → (level r (N / 2 + 1)).card = (level r (N / 2)).card)
    {A : Finset P} (hA : IsMaxAntichain A) :
    A = level r (N / 2) ∨ (N % 2 = 1 ∧ A = level r (N / 2 + 1)) := by
  have hW : A.card = (level r (N / 2)).card :=
    le_antisymm (hwidth A hA.1) (hA.2 _ (isAntichain_level hr _))
  -- no element strictly below the middle
  have hlow : ∀ x ∈ A, N ≤ 2 * r x + 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hx, hxN⟩ := hcon
    obtain ⟨x₀, hx₀, hmin⟩ := Finset.exists_min_image A r ⟨x, hx⟩
    set k := r x₀
    have hk : 2 * k + 1 < N := by have := hmin x hx; omega
    obtain ⟨hanti, hdisj⟩ := shift_up hr hA.1 (k := k) hmin
    have hS : (A.filter fun y => r y = k) ⊆ level r k := fun y hy => by
      rw [mem_level]
      exact (mem_filter.1 hy).2
    have hne : (A.filter fun y => r y = k).Nonempty := ⟨x₀, mem_filter.2 ⟨hx₀, rfl⟩⟩
    have hlt := hup k _ hS hne hk
    have := hwidth _ hanti
    rw [card_union_of_disjoint hdisj] at this
    have := card_split (r := r) A k
    omega
  -- no element strictly above the middle
  have hhigh : ∀ x ∈ A, 2 * r x ≤ N + 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hx, hxN⟩ := hcon
    obtain ⟨x₀, hx₀, hmax⟩ := Finset.exists_max_image A r ⟨x, hx⟩
    set k := r x₀
    have hk : N + 1 < 2 * k := by have := hmax x hx; omega
    obtain ⟨hanti, hdisj⟩ := shift_down hr hA.1 (k := k) (by omega) hmax
    have hS : (A.filter fun y => r y = k) ⊆ level r k := fun y hy => by
      rw [mem_level]
      exact (mem_filter.1 hy).2
    have hne : (A.filter fun y => r y = k).Nonempty := ⟨x₀, mem_filter.2 ⟨hx₀, rfl⟩⟩
    have hlt := hdown k _ hS hne hk
    have := hwidth _ hanti
    rw [card_union_of_disjoint hdisj] at this
    have := card_split (r := r) A k
    omega
  rcases Nat.even_or_odd N with ⟨h, hh⟩ | ⟨h, hh⟩
  · -- even total rank: everything sits in the middle rank
    left
    have hN : N / 2 = h := by omega
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [mem_level]
      have := hlow x hx
      have := hhigh x hx
      omega
    · omega
  · have hN : N / 2 = h := by omega
    have hodd : N % 2 = 1 := by omega
    have hrange : ∀ x ∈ A, r x = h ∨ r x = h + 1 := by
      intro x hx
      have := hlow x hx
      have := hhigh x hx
      omega
    have hsplit := card_split (r := r) A h
    set Ah := A.filter fun x => r x = h
    set Ah1 := A.filter fun x => r x ≠ h
    have hAh1 : Ah1 ⊆ level r (h + 1) := fun y hy => by
      rw [mem_level]
      have := hrange y (mem_filter.1 hy).1
      have := (mem_filter.1 hy).2
      omega
    have hAh : Ah ⊆ level r h := fun y hy => by
      rw [mem_level]
      exact (mem_filter.1 hy).2
    -- elements of `Ah1` avoid the shadow of `Ah`
    have havoid : Disjoint Ah1 (up r Ah h) := by
      rw [Finset.disjoint_left]
      intro y hy hy'
      simp only [up, mem_filter] at hy'
      obtain ⟨-, x, hx, hxy⟩ := hy'
      have hne : x ≠ y := fun e => (mem_filter.1 hy).2 (e ▸ (mem_filter.1 hx).2)
      exact hA.1 (mem_filter.1 hx).1 (mem_filter.1 hy).1 hne hxy
    have hupsub : up r Ah h ⊆ level r (h + 1) := Finset.filter_subset _ _
    have hcard1 : Ah1.card + (up r Ah h).card ≤ (level r (h + 1)).card := by
      rw [← card_union_of_disjoint havoid]
      exact card_le_card (union_subset hAh1 hupsub)
    by_cases hempty : Ah = ∅
    · right
      refine ⟨hodd, ?_⟩
      rw [hN]
      have hsub : A ⊆ level r (h + 1) := by
        intro x hx
        rw [mem_level]
        rcases hrange x hx with e | e
        · exfalso
          have : x ∈ Ah := mem_filter.2 ⟨hx, e⟩
          rw [hempty] at this
          exact absurd this (Finset.notMem_empty x)
        · exact e
      apply Finset.eq_of_subset_of_card_le hsub
      have := hsym hodd
      rw [hN] at this hW
      omega
    · by_cases hfull : Ah = level r h
      · left
        rw [hN]
        have hup' := hupfull hodd
        rw [hN] at hup'
        rw [← hfull] at hup'
        have h1 : Ah1 = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro y hy
          have : y ∈ up r Ah h := by rw [hup']; exact hAh1 hy
          exact Finset.disjoint_left.1 havoid hy this
        have h2 : A = Ah := by
          ext y
          constructor
          · intro hy
            by_contra hy'
            have : y ∈ Ah1 := mem_filter.2 ⟨hy, fun e => hy' (mem_filter.2 ⟨hy, e⟩)⟩
            rw [h1] at this
            exact Finset.notMem_empty y this
          · intro hy
            exact (mem_filter.1 hy).1
        rw [h2, hfull]
      · exfalso
        have hlt := hmid hodd Ah (hN ▸ hAh) (Finset.nonempty_iff_ne_empty.2 hempty)
          (hN ▸ hfull)
        rw [hN] at hlt
        have := hsym hodd
        rw [hN] at this hW
        omega

end Shifting

end DivisorAntichains
