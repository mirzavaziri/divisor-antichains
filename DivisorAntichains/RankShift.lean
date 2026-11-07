/-
The rank shift of the blueprint (Theorem 3.2, step 1).

Let `α` be a finite bounded poset with a strictly monotone rank function `r` such that every
strict inequality `x < y` can be refined by a cover-like step `x < z ≤ y` with `r z = r x + 1`,
and `r ⊥ = 0`. Put `S = r ⊤` and `L = S + t`. Then `c ↦ c + r - S` is a bijection between
strictly antitone maps `α → Fin (L+1)` and antitone maps `α → Fin (t+1)`.
-/
import Mathlib.Order.Antichain
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card

open Finset

namespace DivisorAntichains

section RankShift

variable {α : Type*} [PartialOrder α] [Fintype α] [OrderBot α] [OrderTop α]

omit [Fintype α] [OrderBot α] [OrderTop α] in
/-- Along `x ≤ y`, a strictly antitone map drops by at least the rank difference. -/
theorem drop_le (r : α → ℕ) (hr : StrictMono r)
    (hcov : ∀ x y : α, x < y → ∃ z, x < z ∧ z ≤ y ∧ r z = r x + 1)
    {L : ℕ} {c : α → Fin (L + 1)} (hc : StrictAnti c) :
    ∀ n : ℕ, ∀ x y : α, r y - r x = n → x ≤ y → (c y : ℕ) + (r y - r x) ≤ c x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x y hn hxy
    rcases eq_or_lt_of_le hxy with rfl | hlt
    · simp
    · obtain ⟨z, hxz, hzy, hz⟩ := hcov x y hlt
      have h3 : r z ≤ r y := hr.monotone hzy
      have h4 : r x < r y := hr hlt
      have h1 := ih (r y - r z) (by omega) z y rfl hzy
      have h2 : (c z : ℕ) < c x := hc hxz
      omega

omit [Fintype α] [OrderBot α] [OrderTop α] in
theorem drop_le' (r : α → ℕ) (hr : StrictMono r)
    (hcov : ∀ x y : α, x < y → ∃ z, x < z ∧ z ≤ y ∧ r z = r x + 1)
    {L : ℕ} {c : α → Fin (L + 1)} (hc : StrictAnti c) {x y : α} (hxy : x ≤ y) :
    (c y : ℕ) + (r y - r x) ≤ c x :=
  drop_le r hr hcov hc _ x y rfl hxy

/-- The forward map `c ↦ c + r - r ⊤`. -/
def shiftDown (r : α → ℕ) (hr : StrictMono r)
    (hcov : ∀ x y : α, x < y → ∃ z, x < z ∧ z ≤ y ∧ r z = r x + 1)
    (hbot : r ⊥ = 0) {L t : ℕ} (hL : L = r ⊤ + t)
    (c : α → Fin (L + 1)) (hc : StrictAnti c) : α → Fin (t + 1) :=
  fun x => ⟨(c x : ℕ) + r x - r ⊤, by
    have h1 := drop_le' r hr hcov hc (bot_le : ⊥ ≤ x)
    have h2 := (c ⊥).isLt
    omega⟩

/-- The backward map `v ↦ v + r ⊤ - r`. -/
def shiftUp (r : α → ℕ) {L t : ℕ} (hL : L = r ⊤ + t) (v : α → Fin (t + 1)) :
    α → Fin (L + 1) :=
  fun x => ⟨(v x : ℕ) + r ⊤ - r x, by
    have := (v x).isLt
    omega⟩

open Classical in
/-- Counting form of the rank shift. -/
theorem card_strictAnti_eq_card_antitone (r : α → ℕ) (hr : StrictMono r)
    (hcov : ∀ x y : α, x < y → ∃ z, x < z ∧ z ≤ y ∧ r z = r x + 1)
    (hbot : r ⊥ = 0) {L t : ℕ} (hL : L = r ⊤ + t) :
    (univ.filter fun c : α → Fin (L + 1) => StrictAnti c).card =
      (univ.filter fun v : α → Fin (t + 1) => Antitone v).card := by
  refine Finset.card_bij'
    (fun c hc => shiftDown r hr hcov hbot hL c (mem_filter.1 hc).2)
    (fun v _ => shiftUp r hL v) ?_ ?_ ?_ ?_
  · -- the forward map lands in antitone maps
    intro c hc
    have hc' := (mem_filter.1 hc).2
    refine mem_filter.2 ⟨mem_univ _, fun x y hxy => ?_⟩
    show (⟨_, _⟩ : Fin (t + 1)) ≤ ⟨_, _⟩
    rw [Fin.mk_le_mk]
    have h1 := drop_le' r hr hcov hc' hxy
    have h2 : r x ≤ r y := hr.monotone hxy
    omega
  · -- the backward map lands in strictly antitone maps
    intro v hv
    have hv' := (mem_filter.1 hv).2
    refine mem_filter.2 ⟨mem_univ _, fun x y hxy => ?_⟩
    show (⟨_, _⟩ : Fin (L + 1)) < ⟨_, _⟩
    rw [Fin.mk_lt_mk]
    have h1 : (v y : ℕ) ≤ v x := hv' hxy.le
    have h2 : r x < r y := hr hxy
    have h3 : r y ≤ r ⊤ := hr.monotone le_top
    omega
  · -- left inverse
    intro c hc
    have hc' := (mem_filter.1 hc).2
    funext x
    apply Fin.ext
    show (c x : ℕ) + r x - r ⊤ + r ⊤ - r x = c x
    have h1 := drop_le' r hr hcov hc' (le_top : x ≤ ⊤)
    have h2 : r x ≤ r ⊤ := hr.monotone le_top
    omega
  · -- right inverse
    intro v _
    funext x
    apply Fin.ext
    show (v x : ℕ) + r ⊤ - r x + r x - r ⊤ = v x
    have h2 : r x ≤ r ⊤ := hr.monotone le_top
    omega

section Lemmas

variable (r : α → ℕ) (hr : StrictMono r)
    (hcov : ∀ x y : α, x < y → ∃ z, x < z ∧ z ≤ y ∧ r z = r x + 1)
    (hbot : r ⊥ = 0) {L t : ℕ} (hL : L = r ⊤ + t)

omit [Fintype α] in
@[simp] theorem shiftDown_val (c : α → Fin (L + 1)) (hc : StrictAnti c) (x : α) :
    (shiftDown r hr hcov hbot hL c hc x : ℕ) = c x + r x - r ⊤ := rfl

omit [Fintype α] [OrderBot α] in
@[simp] theorem shiftUp_val (v : α → Fin (t + 1)) (x : α) :
    (shiftUp r hL v x : ℕ) = v x + r ⊤ - r x := rfl

omit [Fintype α] in
include hr hcov in
theorem shiftDown_antitone (c : α → Fin (L + 1)) (hc : StrictAnti c) :
    Antitone (shiftDown r hr hcov hbot hL c hc) := by
  intro x y hxy
  rw [Fin.le_iff_val_le_val, shiftDown_val, shiftDown_val]
  have h1 := drop_le' r hr hcov hc hxy
  have h2 : r x ≤ r y := hr.monotone hxy
  omega

omit [Fintype α] [OrderBot α] in
include hr in
theorem shiftUp_strictAnti (v : α → Fin (t + 1)) (hv : Antitone v) :
    StrictAnti (shiftUp r hL v) := by
  intro x y hxy
  rw [Fin.lt_def, shiftUp_val, shiftUp_val]
  have h1 : (v y : ℕ) ≤ v x := hv hxy.le
  have h2 : r x < r y := hr hxy
  have h3 : r y ≤ r ⊤ := hr.monotone le_top
  omega

omit [Fintype α] in
include hcov in
theorem shiftUp_shiftDown (c : α → Fin (L + 1)) (hc : StrictAnti c) :
    shiftUp r hL (shiftDown r hr hcov hbot hL c hc) = c := by
  funext x
  apply Fin.ext
  rw [shiftUp_val, shiftDown_val]
  have h1 := drop_le' r hr hcov hc (le_top : x ≤ ⊤)
  have h2 : r x ≤ r ⊤ := hr.monotone le_top
  omega

omit [Fintype α] in
theorem shiftDown_shiftUp (v : α → Fin (t + 1)) (hv : StrictAnti (shiftUp r hL v)) :
    shiftDown r hr hcov hbot hL (shiftUp r hL v) hv = v := by
  funext x
  apply Fin.ext
  rw [shiftDown_val, shiftUp_val]
  have h2 : r x ≤ r ⊤ := hr.monotone le_top
  omega

/-- The rank shift as an equivalence between strictly antitone maps into `Fin (L+1)` and
antitone maps into `Fin (t+1)`, where `L = r ⊤ + t`. -/
def shiftEquiv : {c : α → Fin (L + 1) // StrictAnti c} ≃ {v : α → Fin (t + 1) // Antitone v} where
  toFun c := ⟨shiftDown r hr hcov hbot hL c.1 c.2, shiftDown_antitone r hr hcov hbot hL c.1 c.2⟩
  invFun v := ⟨shiftUp r hL v.1, shiftUp_strictAnti r hr hL v.1 v.2⟩
  left_inv c := Subtype.ext (shiftUp_shiftDown r hr hcov hbot hL c.1 c.2)
  right_inv v := Subtype.ext
    (shiftDown_shiftUp r hr hcov hbot hL v.1 (shiftUp_strictAnti r hr hL v.1 v.2))

omit [Fintype α] in
@[simp] theorem shiftEquiv_symm_apply (v : {v : α → Fin (t + 1) // Antitone v}) :
    ((shiftEquiv r hr hcov hbot hL).symm v).1 = shiftUp r hL v.1 := by
  rfl

end Lemmas

end RankShift

end DivisorAntichains
