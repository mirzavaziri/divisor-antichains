/-
Maximum antichains in a product `α × Fin (L+1)` of a finite poset with a chain.

This is the abstract "fiber" argument of the blueprint (Proposition 2.3 and
Theorem 3.1): every antichain meets each fiber `{a} × Fin (L+1)` at most once,
and, as soon as a strictly antitone map `α → Fin (L+1)` exists, the maximum
antichains are exactly the graphs of strictly antitone maps.
-/
import Mathlib.Order.Antichain
import Mathlib.Order.Hom.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Card

open Finset

namespace DivisorAntichains

/-- A finset is a *maximum antichain* if it is an antichain and no antichain is larger. -/
def IsMaxAntichain {β : Type*} [Preorder β] (s : Finset β) : Prop :=
  IsAntichain (· ≤ ·) (s : Set β) ∧
    ∀ t : Finset β, IsAntichain (· ≤ ·) (t : Set β) → t.card ≤ s.card

section Fibers

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α] {L : ℕ}

/-- An antichain of `α × Fin (L+1)` has at most `|α|` elements. -/
theorem card_le_of_isAntichain (s : Finset (α × Fin (L + 1)))
    (hs : IsAntichain (· ≤ ·) (s : Set (α × Fin (L + 1)))) : s.card ≤ Fintype.card α := by
  rw [← Finset.card_univ]
  refine Finset.card_le_card_of_injOn Prod.fst (fun _ _ => Finset.mem_coe.2 (mem_univ _)) ?_
  intro x hx y hy hxy
  by_contra hne
  rcases le_total x.2 y.2 with h | h
  · exact hs hx hy hne (Prod.mk_le_mk.2 ⟨le_of_eq hxy, h⟩)
  · exact hs hy hx (Ne.symm hne) (Prod.mk_le_mk.2 ⟨le_of_eq hxy.symm, h⟩)

/-- The graph `{(a, c a)}` of a map `c : α → Fin (L+1)`. -/
def graph (c : α → Fin (L + 1)) : Finset (α × Fin (L + 1)) :=
  univ.image fun a => (a, c a)

omit [PartialOrder α] in
theorem mem_graph {c : α → Fin (L + 1)} {x : α × Fin (L + 1)} :
    x ∈ graph c ↔ x.2 = c x.1 := by
  constructor
  · intro hx
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
    rfl
  · intro hx
    exact Finset.mem_image.2 ⟨x.1, mem_univ _, by rw [← hx]⟩

omit [PartialOrder α] in
theorem card_graph (c : α → Fin (L + 1)) : (graph c).card = Fintype.card α := by
  rw [graph, Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h), card_univ]

omit [PartialOrder α] in
theorem graph_injective : Function.Injective (graph : (α → Fin (L + 1)) → _) := by
  intro c c' h
  funext a
  have : (a, c a) ∈ graph c' := h ▸ mem_graph.2 rfl
  exact mem_graph.1 this

/-- The graph of `c` is an antichain if and only if `c` is strictly antitone. -/
theorem isAntichain_graph_iff (c : α → Fin (L + 1)) :
    IsAntichain (· ≤ ·) (graph c : Set (α × Fin (L + 1))) ↔ StrictAnti c := by
  constructor
  · intro h a b hab
    by_contra hle
    rw [not_lt] at hle
    have ha : (a, c a) ∈ (graph c : Set _) := mem_graph.2 rfl
    have hb : (b, c b) ∈ (graph c : Set _) := mem_graph.2 rfl
    exact h ha hb (fun e => hab.ne (congrArg Prod.fst e)) (Prod.mk_le_mk.2 ⟨hab.le, hle⟩)
  · intro hc x hx y hy hne hle
    have hx' := mem_graph.1 hx
    have hy' := mem_graph.1 hy
    have h1 : x.1 ≠ y.1 := by
      intro e
      apply hne
      exact Prod.ext e (by rw [hx', hy', e])
    have hlt : x.1 < y.1 := lt_of_le_of_ne (Prod.mk_le_mk.1 hle).1 h1
    have := hc hlt
    rw [← hx', ← hy'] at this
    exact absurd (Prod.mk_le_mk.1 hle).2 (not_le.2 this)

/-- If some strictly antitone map exists, the graph of every strictly antitone map is a
maximum antichain. -/
theorem isMaxAntichain_graph {c : α → Fin (L + 1)} (hc : StrictAnti c) :
    IsMaxAntichain (graph c) :=
  ⟨(isAntichain_graph_iff c).2 hc, fun t ht => (card_graph c).symm ▸ card_le_of_isAntichain t ht⟩

/-- If some strictly antitone map exists, every maximum antichain is a graph. -/
theorem exists_eq_graph_of_isMaxAntichain {c₀ : α → Fin (L + 1)} (hc₀ : StrictAnti c₀)
    {s : Finset (α × Fin (L + 1))} (hs : IsMaxAntichain s) :
    ∃ c, StrictAnti c ∧ s = graph c := by
  classical
  have hcard : s.card = Fintype.card α :=
    le_antisymm (card_le_of_isAntichain s hs.1)
      ((card_graph c₀).symm.le.trans (hs.2 _ ((isAntichain_graph_iff c₀).2 hc₀)))
  -- every fiber is hit
  have himage : s.image Prod.fst = univ := by
    apply Finset.eq_of_subset_of_card_le (subset_univ _)
    rw [card_univ, ← hcard]
    apply le_of_eq
    symm
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    by_contra hne
    rcases le_total x.2 y.2 with h | h
    · exact hs.1 hx hy hne (Prod.mk_le_mk.2 ⟨le_of_eq hxy, h⟩)
    · exact hs.1 hy hx (Ne.symm hne) (Prod.mk_le_mk.2 ⟨le_of_eq hxy.symm, h⟩)
  have hex : ∀ a : α, ∃ i, (a, i) ∈ s := by
    intro a
    have : a ∈ s.image Prod.fst := himage ▸ mem_univ a
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 this
    exact ⟨x.2, hx⟩
  choose c hc using hex
  have hsub : graph c ⊆ s := by
    intro x hx
    rw [mem_graph] at hx
    have := hc x.1
    rwa [← hx] at this
  have heq : graph c = s :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, card_graph])
  refine ⟨c, (isAntichain_graph_iff c).1 ?_, heq.symm⟩
  rw [heq]
  exact hs.1

/-- If some strictly antitone map `α → Fin (L+1)` exists, the width of `α × Fin (L+1)` is `|α|`. -/
theorem width_eq {c₀ : α → Fin (L + 1)} (hc₀ : StrictAnti c₀) :
    (∀ t : Finset (α × Fin (L + 1)),
      IsAntichain (· ≤ ·) (t : Set (α × Fin (L + 1))) → t.card ≤ Fintype.card α) ∧
    ∃ s : Finset (α × Fin (L + 1)),
      IsAntichain (· ≤ ·) (s : Set (α × Fin (L + 1))) ∧ s.card = Fintype.card α :=
  ⟨card_le_of_isAntichain, graph c₀, (isAntichain_graph_iff c₀).2 hc₀, card_graph c₀⟩

open Classical in
/-- Counting form of the fiber theorem: the number of maximum antichains of `α × Fin (L+1)`
equals the number of strictly antitone maps `α → Fin (L+1)`, provided one such map exists. -/
theorem card_maxAntichains {c₀ : α → Fin (L + 1)} (hc₀ : StrictAnti c₀) :
    (univ.filter fun s : Finset (α × Fin (L + 1)) => IsMaxAntichain s).card =
      (univ.filter fun c : α → Fin (L + 1) => StrictAnti c).card := by
  symm
  refine Finset.card_bij (fun c _ => graph c) ?_ ?_ ?_
  · intro c hc
    exact Finset.mem_filter.2 ⟨mem_univ _, isMaxAntichain_graph (Finset.mem_filter.1 hc).2⟩
  · intro c _ c' _ h
    exact graph_injective h
  · intro s hs
    obtain ⟨c, hc, rfl⟩ := exists_eq_graph_of_isMaxAntichain hc₀ (Finset.mem_filter.1 hs).2
    exact ⟨c, Finset.mem_filter.2 ⟨mem_univ _, hc⟩, rfl⟩

/-- The maximum antichains of `α × Fin (L+1)` are in bijection with the strictly antitone maps
`α → Fin (L+1)`, via `c ↦ graph c`, provided one such map exists. -/
noncomputable def graphEquiv {c₀ : α → Fin (L + 1)} (hc₀ : StrictAnti c₀) :
    {c : α → Fin (L + 1) // StrictAnti c} ≃ {s : Finset (α × Fin (L + 1)) // IsMaxAntichain s} where
  toFun c := ⟨graph c.1, isMaxAntichain_graph c.2⟩
  invFun s := ⟨(exists_eq_graph_of_isMaxAntichain hc₀ s.2).choose,
    (exists_eq_graph_of_isMaxAntichain hc₀ s.2).choose_spec.1⟩
  left_inv c := Subtype.ext (graph_injective
    (exists_eq_graph_of_isMaxAntichain hc₀ (isMaxAntichain_graph c.2)).choose_spec.2).symm
  right_inv s := Subtype.ext (exists_eq_graph_of_isMaxAntichain hc₀ s.2).choose_spec.2.symm

@[simp] theorem graphEquiv_apply {c₀ : α → Fin (L + 1)} (hc₀ : StrictAnti c₀)
    (c : {c : α → Fin (L + 1) // StrictAnti c}) : (graphEquiv hc₀ c).1 = graph c.1 := rfl

end Fibers

end DivisorAntichains
