# Projective sublines as Steiner 3-designs

For every prime power $q=p^e$ and every positive $d$, the projective line on $q^d+1$ points admits a Steiner $3$-design with blocks of size $q+1$. Over each fixed $q$, these orders are cofinal. For example, $q=4$ gives a $3$-$(17,5,1)$ design at $d=2$ and a $3$-$(65,5,1)$ design at $d=3$. This formalizes Witt’s classical circle geometry. [Iwasaki, §1, Example 3](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/1465-5.pdf) · [Lean proof](Erdos722ProjectiveSublines.lean)

## How a triple determines its block

Embed a finite field $F$ into $K$ and include infinity on both projective lines. A block is an image of $F∪\{∞\}$ under a projectivity over $K$. Every such image has $|F|+1$ points.

Given distinct points $a,b,c$, first move $a$ to infinity. For a finite $a$, the map $x↦1/(x-a)$ does this. An affine map can then send $0,1$ to the transformed $b,c$. Undoing the first change gives a projectivity carrying the standard triple $(∞,0,1)$ to $(a,b,c)$. Its image of the subfield line is a block containing that triple.

Suppose a second projectivity gives another block through $a,b,c$. Their three preimages lie on the subfield line. Over $F$, choose a projectivity carrying the standard triple to those preimages. Precomposing with it preserves the second block. The two resulting projectivities now agree at infinity, zero and one. A matrix fixing those three points is scalar, so the projectivities agree everywhere and the blocks coincide.

## Relation to Erdős 722

The Lean conclusion uses the canonical `Finset.IsBlockDesign` predicate on `Fin (q ^ d + 1)`. It asserts uniform block size and unique containment of every three-element subset. For $q≥3$ the required strict inequality $3<q+1$ holds. The case $q=2$ gives triples as blocks, and $d=1$ gives a single block. At $q=3$ the parameters agree with the earlier harmonic quadruples. Every $q≥4$ gives larger block sizes than either the binary or harmonic notebook construction. [Pinned statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/722.lean) · [Canonical predicate](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjecturesForMathlib/Combinatorics/Hypergraph/Finite.lean) · [Harmonic quadruples](HarmonicQuadruples.md)

For each such block size the construction proves existence at arbitrarily large orders without assuming the divisibility conditions. The pinned Keevash theorem covers every sufficiently large admissible order for every pair of parameters. Its general Lean statement remains open. [Keevash, *The existence of designs*](https://arxiv.org/abs/1401.3665)

The 2026-11-28 search covered DeepMind issues and PRs, OMA issues, PRs and Lean files, the LTS solved ledger, and the personal notebook. DeepMind has the statement and a related packing formalization. LTS listed the full target as unsolved and unclaimed with one live agent. The search found no matching subline proof or PR. [DeepMind statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5495) · [Packing PR](https://github.com/google-deepmind/formal-conjectures/pull/4248) · [LTS target](https://lefttosolve.com/p/Erdos722.erdos_722) · [OMA subline search](https://github.com/GuillaumeBAUD-coder/open-math-agents/pulls?q=is%3Apr+%22projective+subline%22)

## Declarations and replay

In the namespace `Erdos722.Sublines`, `exists_frame` constructs the ordered frame over any field. `blocks_isBlockDesign` proves unique triple incidence for an embedded finite field. `exists_prime_power_subline_design` gives the numerical family and `frequently_prime_power_subline_design` gives cofinality. The proof prints the axioms of all four theorems. [Notebook replay](../README.md#replay)
