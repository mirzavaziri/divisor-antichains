# Maximum antichains in divisor lattices — Lean 4 formalization

Companion code for the paper by Madjid Mirzavaziri and Daniel Yaqubi (in preparation,
intended for *Annals of Formalized Mathematics*).

The formalization covers the *dominated case* of the blueprint completely: `n = p^L * m` with
`p` prime, `p ∤ m` and `Ω(m) ≤ L`, where `Ω` counts prime factors with multiplicity. For every
`n` it proves the Sperner property of `D(n)` via de Bruijn's symmetric chain decomposition.
For the balanced case it proves that the strict expansion property `UpExpansion n` (the core
of Griggs's theorem) implies that the maximum antichains are exactly the middle ranks. It also
proves that the rank sizes of a balanced divisor lattice increase strictly up to the middle, and
reduces `UpExpansion n` to the normalized matching property of `D(n)` plus, when `Ω(n)` is odd,
one expansion step between the two middle ranks. For squarefree `n` both are proved, so
`a_of_squarefree` holds without hypotheses. Every
result is proved without `sorry` and depends only on the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Building

```
lake exe cache get   # optional: downloads prebuilt Mathlib
lake build
```

Toolchain: `leanprover/lean4:v4.36.0-rc2`.
Mathlib: commit `6db5db0d2279846cc8fb25901bd53221d37a77d8` (6 Nov 2026).

## Main definitions

| Lean | Meaning |
|---|---|
| `Div n` | the divisors of `n`, ordered by divisibility |
| `Div.rank` | `Ω`, the rank function of `Div n` |
| `IsMaxAntichain s` | `s` is an antichain and no antichain is larger |
| `a n` | number of maximum antichains of `Div n` (OEIS A096826) |
| `numAntichains n` | number of antichains of `Div n`, including the empty one (OEIS A096827) |
| `g n` | maximum antichains with lcm `n` (maximum families of subgroups generating `ℤ/nℤ`) |
| `gStar n` | maximum antichains with lcm `n` and gcd `1` |

## Correspondence with the paper

| Paper | Lean | File |
|---|---|---|
| Prop. 2.3 (width `d(m)` in the dominated case) | `width_dominated` | `Main.lean` |
| Prop. 2.3, abstract form | `card_le_of_isAntichain`, `width_eq` | `Fibers.lean` |
| Thm. 3.1 (maximum antichains ↔ strictly antitone maps) | `graphEquiv`, `card_maxAntichains` | `Fibers.lean` |
| Thm. 3.2, step 1 (rank shift) | `shiftEquiv`, `card_strictAnti_eq_card_antitone` | `RankShift.lean` |
| `D(p^L m) ≃o D(m) × C_{L+1}` | `decomp` | `Divisors.lean` |
| Thm. 3.2, `a(n) = Φ_m(t)` | `a_dominated`, `maxAntichainEquiv` | `Main.lean` |
| Thm. 3.2, steps 2–3 (lower sets, antichains, A096827) | `antitoneLowerEquiv`, `antichainLowerEquiv`, `a_eq_numAntichains` | `Ideals.lean` |
| Cor. 3.3(a) (two primes, `binomial(L+1, s+1)`) | `a_two_primes` | `Binomial.lean` |
| Cor. 3.3(c) (Dedekind numbers) | `a_pow_succ_eq_numAntichains` | `Ideals.lean` |
| Thm. 4.1, lcm and gcd conditions | `lcm_graph_eq_iff`, `gcd_graph_eq_iff` | `Groups.lean` |
| Thm. 4.1, counts of `g` and `g*` | `g_dominated`, `gStar_dominated` | `Groups.lean` |
| Thm. 4.1, `g(n) = a(n) − a(n/p)` | `g_add_a_pred` | `Groups.lean` |
| Thm. 4.1, `g*(n) = a(n) − 2a(n/p) + a(n/p²)` | `card_antitone_second_difference`, `gStar_add_two_a` | `Groups.lean` |
| Numerical checks (`a(48) = 10`, …) | examples | `Examples.lean` |
| Thm. 2.2 (symmetric chain decomposition of `D(n)`) | `SCD`, `SCD.prod`, `nonempty_scd` | `SymmetricChains.lean` |
| Thm. 2.2 (Sperner: width = middle rank) | `card_le_midRank`, `isMaxAntichain_midRank` | `SymmetricChains.lean` |
| Lemma 3.4, reduction by shifting (abstract) | `shift_up`, `shift_down`, `eq_level_of_isMaxAntichain` | `Shifting.lean` |
| Lemma 3.4, balanced case under strict expansion | `UpExpansion`, `eq_middle_of_upExpansion`, `a_of_upExpansion` | `Balanced.lean` |
| Rank symmetry and downward expansion by `d ↦ n/d` | `card_level_compl`, `down_expansion` | `Balanced.lean` |
| Prop. 3.5 (strict growth of rank sizes up to the middle) | `lv_lt_succ`, `lv_lt_succ_of_balanced` | `NormalizedMatching.lean` |
| Prop. 3.5, recursion `N_{k+1}(p^L m) + N_{k-L}(m) = N_k(p^L m) + N_{k+1}(m)` | `lv_peel` | `NormalizedMatching.lean` |
| Squarefree `n`: local LYM and Sperner's theorem with its extremal families | `normalizedMatching_of_squarefree`, `upExpansion_of_squarefree`, `a_of_squarefree` | `Squarefree.lean` |
| Cor. 3.6, balanced case from normalized matching | `upExpansion_of_normalizedMatching`, `a_of_normalizedMatching`, `a_of_normalizedMatching_even` | `NormalizedMatching.lean` |

## Not formalized (cited in the paper)

* For balanced `n` that is not squarefree: the normalized matching property `NormalizedMatching n` of `D(n)` (Hsieh–Kleitman 1973,
  Harper 1974), and, for odd `Ω(n)`, strict expansion between the two middle ranks
  (`MiddleExpansion n`). The theorems `a_of_normalizedMatching` and
  `a_of_normalizedMatching_even` take these as hypotheses; for even `Ω(n)` only the first is
  needed.
* MacMahon's box formula (Cor. 3.3(b)) and polynomiality of order polynomials (Cor. 3.3(d)).

## License

Apache License 2.0, the same license as Mathlib. See `LICENSE`.

## How to cite

See `CITATION.cff`. A DOI for each release is provided by Zenodo.
