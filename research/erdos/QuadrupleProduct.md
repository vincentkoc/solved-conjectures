# Products of Steiner quadruple systems

If there are Steiner quadruple systems on $m$ and $n$ points, there is one on $mn$ points. Iterating the construction with the ten-point harmonic system gives every order $10^d$ for $d≥1$. For $d≥3$ these orders are outside both earlier quadruple-system families, $2^i$ and $3^i+1$. Alexander Rosa describes the classical multiplication of orders through ternary Steiner quasigroups. [Rosa, *Combinatorial Design Theory — Notes*, §IV](https://kam.mff.cuni.cz/conferences/ATCAGC_2014/materialy/Combinatorial_Designs_Notes.pdf) · [Lean proof](Erdos722QuadrupleProduct.lean)

## Completing a triple in the product

Take the Cartesian product of the two point sets. For each four-element subset, project its points onto each factor **with multiplicities**. Accept a projection if its support is a block of the factor design or if every multiplicity is even. The four-element subset is a product block exactly when both projections pass this test.

Three entries in a single coordinate determine a unique fourth entry. If all three are distinct, the unique containing block in the factor determines it. If two entries coincide, completing the two equal pairs forces the remaining entry. This rule also handles three equal entries.

Complete both coordinates of a triple of distinct product points. The resulting point is fresh. For example, if the fourth point equalled the first, each coordinate projection would contain the first coordinate twice. The pairing rule would then force the second and third points to agree in both coordinates, contradicting distinctness of the original points. Coordinate uniqueness now proves block uniqueness.

## Orders and scope

The order-ten seed comes from the earlier harmonic construction with extension degree two. The product gives $10^{d+1}$ from $10^d$ and $10$. Every $10^d$ with $d≥3$ has a factor of five and is divisible by eight. Powers of three are 1 or 3 modulo eight, so $3^i+1$ is never divisible by eight. In the broader projective-subline construction the only block size four occurs at $q=3$, which has those same ternary orders. [Harmonic seed](HarmonicQuadruples.md) · [Projective sublines](ProjectiveSublines.md)

The result uses the pinned `Finset.IsBlockDesign 3 4` predicate on `Fin (m * n)`. The final cofinality theorem gives, above each cutoff, an order outside both earlier families and an actual design on it. The upstream theorem requires all sufficiently large admissible orders for every pair of parameters. Hanani established the full quadruple-system spectrum, and Keevash proved the general design existence theorem. [Pinned Erdős 722](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/722.lean) · [Rosa, §IV](https://kam.mff.cuni.cz/conferences/ATCAGC_2014/materialy/Combinatorial_Designs_Notes.pdf)

## Verification

In `Erdos722.QuadrupleProduct`, `blocks_isBlockDesign` verifies the labelled construction, `exists_product` proves multiplicative closure, `exists_ten_power` constructs the family, `ten_power_new_orders` proves the arithmetic exclusions, and `arbitrarily_large_mixed_orders` combines existence and cofinality. A clean build compiled the harmonic dependency and product module with warnings as errors. Independent `leanchecker` replay passed for both. The five product declarations report only `propext`, `Classical.choice` and `Quot.sound`. [Notebook replay](../README.md#replay)

The 2026-11-28 checks covered DeepMind issues and PRs, LTS and OMA, including open PR source. LTS listed the target as unsolved and unclaimed. An open Alspach PR already contained Bose and Skolem triple-system constructions. The search found no matching quadruple-system product formalization. [DeepMind statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5495) · [LTS target](https://lefttosolve.com/p/Erdos722.erdos_722) · [OMA Alspach PR](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/12713) · [OMA quadruple-system search](https://github.com/GuillaumeBAUD-coder/open-math-agents/pulls?q=is%3Apr+%22Steiner+quadruple%22)
