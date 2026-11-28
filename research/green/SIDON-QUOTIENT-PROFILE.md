# One quarter of the sums are missing in dense order-two Sidon quotients

Let `A` be a Sidon set modulo `2M`, and let `B` be its image modulo `M`. Along every sequence with `M → ∞` and `|A|/√M → √2`, the fractions of residues with exactly zero, two and four **ordered** representations in `B+B` tend to `1/4, 1/2, 1/4`, respectively. For every odd prime `p`, Ruzsa’s cyclic Sidon construction realizes the hypotheses at `M = p(p−1)/2` with `p−1` labels. Each residue has at most two **unordered** representations, including diagonals. [Lean proof](Green33SidonProfile.lean)

Sándor and Yang’s theorem 1(a) gives at least `M/4 − √(5M)` missing residues for every finite abelian group with ordered representation counts at most five. Their theorem 1(b) exhibits cyclic examples with fewer than `3M/8` missing. The family above attains the lower bound’s leading constant already with ordered cap four. The seed is Ruzsa’s and its modular quotient is the case `g = 2` of the construction of Caicedo, Gómez, Gómez and Trujillo, theorem 2 and corollary 3. The result here computes the limiting distribution for all dense order-two projections. [Sándor–Yang, theorem 1](https://arxiv.org/pdf/1705.03316#page=2) · [Caicedo et al., theorem 2](https://arxiv.org/pdf/1411.5741#page=7)

## Proof and finite error

The seed consists of the points `(a,a)` in `𝔽ₚˣ × 𝔽ₚ`, with multiplication in the first coordinate and addition in the second. A pair sum determines the product and the sum of its field entries, hence the unordered pair. The cyclicity of the units and the Chinese remainder theorem give the cyclic seed of order `p(p−1)`. The Lean statement uses the pinned upstream predicate `IsSidon`, whose equality cases are exactly the two permutations. [Pinned predicate](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjecturesForMathlib/Combinatorics/Basic.lean)

Projection preserves the size of any Sidon seed because labels with the same image have equal doubles upstairs. Each quotient sum lifts to at most two sums, and each nonzero quotient difference lifts to at most two nonzero differences. Thus ordered sums are bounded by four and nonzero ordered differences by two.

Write `m = |G|`, `k = |B|`, and let `Sⱼ` count residues with exactly `j` ordered representations. The generic theorem `profile_error` only needs the two ordered caps above. The centered sum energy lies between `(k−2)²` and `4m−k²−2k`. To see the upper bound, transfer the energy to differences, keep the zero difference separately, and use `(d−2)² ≤ 2(2−d)` for every other difference count `d`. Odd sum counts can occur only at doubles. The total mass, total count and centered energy then give the simultaneous bound

```text
max(|4S₀−m|, |2S₂−m|, |4S₄−m|) ≤ 4|k²−2m| + 10k + 4.
```

For the prime family the right side is `14(p−1)+4`. This yields an error of order `√M` in counts. [Finite and limiting theorems](Green33SidonProfile.lean) · [Sum and difference energy](TAIL-ENERGY.md)

## Consequence for Green 33

For any two sets `A,B` in the same finite abelian group, every sum in `(B+B) ∖ (A+A)` lies in `(B ∖ A)+B`. Thus adding `t` new labels fills at most `t|B|` old holes, even with arbitrary deletions. At the size in Green 33, changing a projected seed by adding `o(√M)` labels leaves the missing fraction eventually greater than every fixed number below `1/4`. This rules out such repairs for full and approximate covers. The pinned question asks for full coverage and the same limiting size along arbitrarily large positive moduli. Other constructions remain open. [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Approximate-cover equivalence](APPROXIMATE-COVERS.md)

All nine public theorems print only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the formalization. [Replay instructions](../README.md#replay)
