/-
Generating and co-generating maximum antichains (blueprint, Section 4).

Identify the divisor `d ∣ n` with the subgroup of `ℤ/nℤ` of order `d`. A family of subgroups
generates `ℤ/nℤ` iff the lcm of the orders is `n`, and has trivial intersection iff their gcd
is `1`. In the dominated case we characterise both conditions on the antitone map side:
the lcm condition says that the map takes its largest value at `1`, and the gcd condition says
that it takes the value `0` at `m`.
-/
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.SetTheory.Cardinal.Finite
import DivisorAntichains.Main

open Finset

namespace DivisorAntichains

variable {p m L : ℕ}

theorem decomp_apply_val (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m ≠ 0) (x : Div m × Fin (L + 1)) :
    ((decomp (L := L) hp hpm hm) x).1 = x.1.1 * p ^ (x.2 : ℕ) := rfl

theorem mem_graph_map {hp : p.Prime} {hpm : ¬ p ∣ m} {hm : m ≠ 0} {c : Div m → Fin (L + 1)}
    {d : Div (p ^ L * m)} :
    d ∈ (graph c).map (decomp hp hpm hm).toEquiv.toEmbedding ↔
      ∃ q : Div m, d.1 = q.1 * p ^ (c q : ℕ) := by
  constructor
  · intro hd
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hd
    refine ⟨x.1, ?_⟩
    rw [mem_graph] at hx
    show ((decomp hp hpm hm) x).1 = _
    rw [decomp_apply_val, hx]
  · rintro ⟨q, hq⟩
    refine Finset.mem_map.2 ⟨(q, c q), mem_graph.2 rfl, Subtype.ext ?_⟩
    show ((decomp hp hpm hm) (q, c q)).1 = d.1
    rw [decomp_apply_val, hq]

theorem graph_map_mem (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m ≠ 0) (c : Div m → Fin (L + 1))
    (q : Div m) :
    (decomp hp hpm hm) (q, c q) ∈ (graph c).map (decomp hp hpm hm).toEquiv.toEmbedding :=
  Finset.mem_map_of_mem _ (mem_graph.2 rfl)

/-- The antichain attached to `c` generates (lcm `= p^L m`) iff `c 1 = L`. -/
theorem lcm_graph_eq_iff (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m ≠ 0) [NeZero m]
    {c : Div m → Fin (L + 1)} (hc : StrictAnti c) :
    ((graph c).map (decomp hp hpm hm).toEquiv.toEmbedding).lcm (fun d => d.1) = p ^ L * m ↔
      c ⊥ = Fin.last L := by
  set s := (graph c).map (decomp hp hpm hm).toEquiv.toEmbedding
  have hle : s.lcm (fun d => d.1) ∣ p ^ L * m := Finset.lcm_dvd fun d _ => Div.val_dvd d
  constructor
  · intro h
    by_contra hne
    have hlt : (c ⊥ : ℕ) < L := Fin.val_lt_last hne
    have hdvd : s.lcm (fun d => d.1) ∣ m * p ^ (L - 1) := by
      apply Finset.lcm_dvd
      intro d hd
      obtain ⟨q, hq⟩ := mem_graph_map.1 hd
      rw [hq]
      have h1 : (c q : ℕ) ≤ c ⊥ := hc.antitone bot_le
      exact mul_dvd_mul (Div.val_dvd q) (pow_dvd_pow p (by omega))
    rw [h] at hdvd
    have h3 : p ^ (L - 1) < p ^ L := Nat.pow_lt_pow_right hp.one_lt (by omega)
    have h4 : m * p ^ (L - 1) < p ^ L * m := by
      rw [mul_comm m]
      exact Nat.mul_lt_mul_of_pos_right h3 (Nat.pos_of_ne_zero hm)
    have h5 := Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero hm) (pow_pos hp.pos _)) hdvd
    omega
  · intro h
    apply Nat.dvd_antisymm hle
    have hcop : Nat.Coprime (p ^ L) m :=
      Nat.Coprime.pow_left L ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm)
    apply hcop.mul_dvd_of_dvd_of_dvd
    · have := Finset.dvd_lcm (f := fun d : Div (p ^ L * m) => d.1) (graph_map_mem hp hpm hm c ⊥)
      rw [decomp_apply_val, h, Fin.val_last] at this
      simpa using this
    · have := Finset.dvd_lcm (f := fun d : Div (p ^ L * m) => d.1) (graph_map_mem hp hpm hm c ⊤)
      rw [decomp_apply_val] at this
      exact dvd_trans (dvd_mul_right _ _) this

/-- The antichain attached to `c` has gcd `1` iff `c m = 0`. -/
theorem gcd_graph_eq_iff (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m ≠ 0) [NeZero m]
    {c : Div m → Fin (L + 1)} (hc : StrictAnti c) :
    ((graph c).map (decomp hp hpm hm).toEquiv.toEmbedding).gcd (fun d => d.1) = 1 ↔
      c ⊤ = 0 := by
  set s := (graph c).map (decomp hp hpm hm).toEquiv.toEmbedding
  constructor
  · intro h
    by_contra hne
    have hpos : (c ⊤ : ℕ) ≠ 0 := fun h0 => hne (Fin.ext (by simpa using h0))
    have hdvd : p ∣ s.gcd (fun d => d.1) := by
      apply Finset.dvd_gcd
      intro d hd
      obtain ⟨q, hq⟩ := mem_graph_map.1 hd
      rw [hq]
      have h1 : (c ⊤ : ℕ) ≤ c q := hc.antitone le_top
      exact dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) _
    rw [h] at hdvd
    exact hp.one_lt.ne' (Nat.dvd_one.1 hdvd)
  · intro h
    have h1 := Finset.gcd_dvd (f := fun d : Div (p ^ L * m) => d.1) (graph_map_mem hp hpm hm c ⊤)
    have h2 := Finset.gcd_dvd (f := fun d : Div (p ^ L * m) => d.1) (graph_map_mem hp hpm hm c ⊥)
    rw [decomp_apply_val, h] at h1
    rw [decomp_apply_val] at h2
    simp only [Fin.val_zero, pow_zero, mul_one, Div.top_val] at h1
    simp only [Div.bot_val, one_mul] at h2
    have hcop : Nat.Coprime m (p ^ (c ⊥ : ℕ)) :=
      Nat.Coprime.pow_right _ (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm))
    have := Nat.dvd_gcd h1 h2
    rw [hcop.gcd_eq_one] at this
    exact Nat.dvd_one.1 this

open Classical in
/-- `g n`: maximum antichains of `D(n)` with lcm `n`, i.e. maximum families of subgroups of
`ℤ/nℤ`, none containing another, that generate `ℤ/nℤ`. -/
noncomputable def g (n : ℕ) : ℕ :=
  Fintype.card {s : Finset (Div n) // IsMaxAntichain s ∧ s.lcm (fun d => d.1) = n}

open Classical in
/-- `gStar n`: maximum antichains of `D(n)` with lcm `n` and gcd `1`. -/
noncomputable def gStar (n : ℕ) : ℕ :=
  Fintype.card {s : Finset (Div n) //
    IsMaxAntichain s ∧ s.lcm (fun d => d.1) = n ∧ s.gcd (fun d => d.1) = 1}

/-- The value of the shifted map at `1`. -/
theorem shiftUp_bot_val [NeZero m] {t : ℕ} (hLt : L = Div.rank (⊤ : Div m) + t)
    (v : Div m → Fin (t + 1)) :
    (shiftUp Div.rank hLt v ⊥ : ℕ) = v ⊥ + ArithmeticFunction.cardFactors m := by
  rw [shiftUp_val, Div.rank_bot, Div.rank_top]
  omega

/-- The value of the shifted map at `m`. -/
theorem shiftUp_top_val [NeZero m] {t : ℕ} (hLt : L = Div.rank (⊤ : Div m) + t)
    (v : Div m → Fin (t + 1)) :
    (shiftUp Div.rank hLt v ⊤ : ℕ) = v ⊤ := by
  rw [shiftUp_val]
  omega

open Classical in
/-- **Generating maximum antichains (dominated case).** -/
theorem g_dominated (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m ≠ 0) [NeZero m]
    (hL : ArithmeticFunction.cardFactors m ≤ L) :
    g (p ^ L * m) =
      Fintype.card {v : Div m → Fin (L - ArithmeticFunction.cardFactors m + 1) //
        Antitone v ∧ v ⊥ = Fin.last _} := by
  set E := maxAntichainEquiv hp hpm hm hL
  have key : ∀ v : {v : Div m → Fin (L - ArithmeticFunction.cardFactors m + 1) // Antitone v},
      v.1 ⊥ = Fin.last _ ↔ (E v).1.lcm (fun d => d.1) = p ^ L * m := by
    intro v
    have hsa := shiftUp_strictAnti Div.rank Div.rank_strictMono (L_eq_rank_top hL) v.1 v.2
    rw [maxAntichainEquiv_apply, lcm_graph_eq_iff hp hpm hm hsa, Fin.ext_iff, Fin.ext_iff,
      Fin.val_last, Fin.val_last, shiftUp_bot_val]
    omega
  unfold g
  exact Fintype.card_congr
    (((Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans (E.subtypeEquiv key)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _)).symm

open Classical in
/-- **Generating maximum antichains with trivial intersection (dominated case).** -/
theorem gStar_dominated (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m ≠ 0) [NeZero m]
    (hL : ArithmeticFunction.cardFactors m ≤ L) :
    gStar (p ^ L * m) =
      Fintype.card {v : Div m → Fin (L - ArithmeticFunction.cardFactors m + 1) //
        Antitone v ∧ (v ⊥ = Fin.last _ ∧ v ⊤ = 0)} := by
  set E := maxAntichainEquiv hp hpm hm hL
  have key : ∀ v : {v : Div m → Fin (L - ArithmeticFunction.cardFactors m + 1) // Antitone v},
      (v.1 ⊥ = Fin.last _ ∧ v.1 ⊤ = 0) ↔
        ((E v).1.lcm (fun d => d.1) = p ^ L * m ∧ (E v).1.gcd (fun d => d.1) = 1) := by
    intro v
    have hsa := shiftUp_strictAnti Div.rank Div.rank_strictMono (L_eq_rank_top hL) v.1 v.2
    rw [maxAntichainEquiv_apply, lcm_graph_eq_iff hp hpm hm hsa, gcd_graph_eq_iff hp hpm hm hsa,
      Fin.ext_iff, Fin.ext_iff, Fin.ext_iff, Fin.ext_iff, Fin.val_last, Fin.val_last,
      shiftUp_bot_val, shiftUp_top_val, Fin.val_zero, Fin.val_zero]
    omega
  unfold gStar
  exact Fintype.card_congr
    (((Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans (E.subtypeEquiv key)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _)).symm


section Difference

open Classical in
/-- Antitone maps into `Fin (t+1)` split according to whether they take the top value at `⊥`;
those that do not are exactly the antitone maps into `Fin t`. -/
theorem card_antitone_split {α : Type*} [PartialOrder α] [OrderBot α] [Fintype α]
    (t : ℕ) :
    Fintype.card {v : α → Fin (t + 1) // Antitone v} =
      Fintype.card {v : α → Fin (t + 1) // Antitone v ∧ v ⊥ = Fin.last t} +
        Fintype.card {w : α → Fin t // Antitone w} := by
  have e1 : {v : α → Fin (t + 1) // Antitone v ∧ ¬ v ⊥ = Fin.last t} ≃
      {w : α → Fin t // Antitone w} :=
    { toFun := fun v => ⟨fun x => Fin.castLT (v.1 x) (by
          have h1 : (v.1 x : ℕ) ≤ v.1 ⊥ := v.2.1 bot_le
          have h2 : (v.1 ⊥ : ℕ) < t := Fin.val_lt_last v.2.2
          omega), fun x y hxy => by
          rw [Fin.le_iff_val_le_val]
          exact v.2.1 hxy⟩
      invFun := fun w => ⟨fun x => Fin.castSucc (w.1 x),
        ⟨fun x y hxy => Fin.castSucc_le_castSucc_iff.2 (w.2 hxy),
          (Fin.castSucc_lt_last _).ne⟩⟩
      left_inv := fun v => by
        apply Subtype.ext
        funext x
        rfl
      right_inv := fun w => by
        apply Subtype.ext
        funext x
        rfl }
  rw [← Fintype.card_congr e1]
  rw [← Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun v : α → Fin (t + 1) =>
      Antitone v) (fun v => v ⊥ = Fin.last t)),
    ← Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun v : α → Fin (t + 1) =>
      Antitone v) (fun v => ¬ v ⊥ = Fin.last t))]
  rw [← Fintype.card_sum]
  exact Fintype.card_congr (Equiv.sumCompl _).symm

open Classical in
theorem card_antitone_congr {α : Type*} [PartialOrder α] [Fintype α] {a b : ℕ}
    (h : a = b) :
    Fintype.card {v : α → Fin a // Antitone v} = Fintype.card {v : α → Fin b // Antitone v} := by
  subst h
  rfl

open Classical in
theorem a_eq_card (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m ≠ 0)
    (hL : ArithmeticFunction.cardFactors m ≤ L) :
    a (p ^ L * m) =
      Fintype.card {v : Div m → Fin (L - ArithmeticFunction.cardFactors m + 1) // Antitone v} := by
  rw [a_dominated hp hpm hm hL, Fintype.card_subtype]

open Classical in
/-- **`g(n) = a(n) - a(n/p)` in the strictly dominated case.** If `Ω(m) < L`, then
`g(p^L m) + a(p^(L-1) m) = a(p^L m)`. -/
theorem g_add_a_pred (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m ≠ 0) [NeZero m]
    (hL : ArithmeticFunction.cardFactors m < L) :
    g (p ^ L * m) + a (p ^ (L - 1) * m) = a (p ^ L * m) := by
  have h1 := card_antitone_split (α := Div m) (L - ArithmeticFunction.cardFactors m)
  have h2 := card_antitone_congr (α := Div m) (show L - 1 - ArithmeticFunction.cardFactors m + 1 =
    L - ArithmeticFunction.cardFactors m by omega)
  rw [g_dominated hp hpm hm hL.le, a_eq_card hp hpm hm hL.le, a_eq_card hp hpm hm (by omega)]
  simp only [Fintype.card_eq_nat_card] at h1 h2 ⊢
  omega

open Classical in
/-- Among antitone maps into `Fin (s+2)` taking the top value at `⊥`, those that do not vanish at
`⊤` are, after subtracting one, the antitone maps into `Fin (s+1)` taking the top value at `⊥`. -/
theorem card_antitone_split_top {α : Type*} [PartialOrder α] [OrderBot α] [OrderTop α]
    [Fintype α] (s : ℕ) :
    Fintype.card {v : α → Fin (s + 1 + 1) // Antitone v ∧ (v ⊥ = Fin.last _ ∧ v ⊤ = 0)} +
        Fintype.card {w : α → Fin (s + 1) // Antitone w ∧ w ⊥ = Fin.last _} =
      Fintype.card {v : α → Fin (s + 1 + 1) // Antitone v ∧ v ⊥ = Fin.last _} := by
  have hne : ∀ (v : α → Fin (s + 1 + 1)), Antitone v → ¬ v ⊤ = 0 → ∀ x, v x ≠ 0 := by
    intro v hv h0 x hx
    have h1 : (v ⊤ : ℕ) ≤ v x := hv le_top
    rw [hx] at h1
    exact h0 (Fin.ext (by simp at h1; simpa using h1))
  have e1 : {v : α → Fin (s + 1 + 1) // (Antitone v ∧ v ⊥ = Fin.last _) ∧ ¬ v ⊤ = 0} ≃
      {w : α → Fin (s + 1) // Antitone w ∧ w ⊥ = Fin.last _} :=
    { toFun := fun v => ⟨fun x => (v.1 x).pred (hne v.1 v.2.1.1 v.2.2 x), fun x y hxy => by
          rw [Fin.le_iff_val_le_val, Fin.val_pred, Fin.val_pred]
          have := v.2.1.1 hxy
          rw [Fin.le_iff_val_le_val] at this
          omega, by
          apply Fin.ext
          rw [Fin.val_pred, v.2.1.2]
          simp⟩
      invFun := fun w => ⟨fun x => (w.1 x).succ,
        ⟨⟨fun x y hxy => Fin.succ_le_succ_iff.2 (w.2.1 hxy), by
          apply Fin.ext
          rw [Fin.val_succ, w.2.2]
          simp⟩, Fin.succ_ne_zero _⟩⟩
      left_inv := fun v => by
        apply Subtype.ext
        funext x
        have h0 := hne v.1 v.2.1.1 v.2.2 x
        have h0' : (v.1 x : ℕ) ≠ 0 := fun e => h0 (Fin.ext e)
        apply Fin.ext
        simp only [Fin.val_succ, Fin.val_pred]
        omega
      right_inv := fun w => by
        apply Subtype.ext
        funext x
        apply Fin.ext
        simp only [Fin.val_succ, Fin.val_pred]
        omega }
  rw [← Fintype.card_congr e1]
  rw [← Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun v : α → Fin (s + 1 + 1) => Antitone v ∧ v ⊥ = Fin.last _) (fun v => ¬ v ⊤ = 0))]
  have e2 : {v : α → Fin (s + 1 + 1) // Antitone v ∧ (v ⊥ = Fin.last _ ∧ v ⊤ = 0)} ≃
      {v : {v : α → Fin (s + 1 + 1) // Antitone v ∧ v ⊥ = Fin.last _} // v.1 ⊤ = 0} :=
    { toFun := fun v => ⟨⟨v.1, v.2.1, v.2.2.1⟩, v.2.2.2⟩
      invFun := fun v => ⟨v.1.1, v.1.2.1, v.1.2.2, v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e2, ← Fintype.card_sum]
  exact Fintype.card_congr (Equiv.sumCompl _)

open Classical in
/-- The second difference: `G(k) + 2 A(k-1) = A(k) + A(k-2)` for `k ≥ 2`, where `A(k)` counts
antitone maps into `Fin (k+1)` and `G(k)` those with value `k` at `⊥` and `0` at `⊤`. -/
theorem card_antitone_second_difference {α : Type*} [PartialOrder α] [OrderBot α] [OrderTop α]
    [Fintype α] {k : ℕ} (hk : 2 ≤ k) :
    Fintype.card {v : α → Fin (k + 1) // Antitone v ∧ (v ⊥ = Fin.last _ ∧ v ⊤ = 0)} +
        2 * Fintype.card {v : α → Fin (k - 1 + 1) // Antitone v} =
      Fintype.card {v : α → Fin (k + 1) // Antitone v} +
        Fintype.card {v : α → Fin (k - 2 + 1) // Antitone v} := by
  obtain ⟨s, rfl⟩ : ∃ s, k = s + 2 := ⟨k - 2, by omega⟩
  rw [show s + 2 = s + 1 + 1 from rfl]
  have c1 := card_antitone_congr (α := α) (show s + 1 + 1 - 1 + 1 = s + 1 + 1 by omega)
  have c2 := card_antitone_congr (α := α) (show s + 1 + 1 - 2 + 1 = s + 1 by omega)
  rw [c1, c2]
  have h1 := card_antitone_split (α := α) (s + 1 + 1)
  have h2 := card_antitone_split (α := α) (s + 1)
  have h5 := card_antitone_split_top (α := α) (s + 1)
  simp only [Fintype.card_eq_nat_card] at h1 h2 h5 ⊢
  omega

open Classical in
/-- **The second-difference formula for `g*`.** If `Ω(m) + 2 ≤ L`, then
`g*(p^L m) + 2 a(p^(L-1) m) = a(p^L m) + a(p^(L-2) m)`. -/
theorem gStar_add_two_a (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m ≠ 0) [NeZero m]
    (hL : ArithmeticFunction.cardFactors m + 2 ≤ L) :
    gStar (p ^ L * m) + 2 * a (p ^ (L - 1) * m) = a (p ^ L * m) + a (p ^ (L - 2) * m) := by
  have h := card_antitone_second_difference (α := Div m)
    (k := L - ArithmeticFunction.cardFactors m) (by omega)
  have c1 := card_antitone_congr (α := Div m) (show L - ArithmeticFunction.cardFactors m - 1 + 1 =
    L - 1 - ArithmeticFunction.cardFactors m + 1 by omega)
  have c2 := card_antitone_congr (α := Div m) (show L - ArithmeticFunction.cardFactors m - 2 + 1 =
    L - 2 - ArithmeticFunction.cardFactors m + 1 by omega)
  rw [gStar_dominated hp hpm hm (by omega), a_eq_card hp hpm hm (by omega),
    a_eq_card hp hpm hm (by omega), a_eq_card hp hpm hm (by omega)]
  rw [c1, c2] at h
  simp only [Fintype.card_eq_nat_card] at h ⊢
  omega

end Difference

end DivisorAntichains
