# Cube exclusion for the product of the Hosoya neighbors

For every positive index `n`, the product of `Fₙ+Lₙ₊₁` and `Fₙ+Lₙ₋₁` is never a cube. The argument removes the integral-point assumption on the Mordell curve `Y²=X³+1331` from the earlier product theorem. Its exclusion of **all** proper powers now needs just the stated coefficient-eleven case of Bennett and Skinner. [Product proof](HosoyaNeighborCubesUnconditional.lean) · [Earlier hypotheses](PowersAndPrivatePrimeDivisors.md) · [Ching et al., neighboring prime values](https://arxiv.org/abs/2211.10788)

The proof gives two independent statements. For all integers `f,y` with `18 ∣ f`, the equation `y³+1=11f²` forces `(f,y)=(0,−1)`. For every Fibonacci index `n ≥ 0`, the equation `y³+1=11Fₙ²` has no nonnegative solution `y`. These statements concern a subset of the integral points used in the earlier argument. [Quadratic-ring descent](HosoyaProductCubeDescent.lean) · [Fibonacci specialization](HosoyaNeighborCubesUnconditional.lean) · [Bennett and Ghadermarzi’s row 1331](https://personal.math.ubc.ca/~bennett/0-10%5E6n.pdf#page=13)

## The descent modulo nine

In `ℤ[√11]`, write `z=1+f√11`. Its norm is `−y³`. Any common divisor of `z` and its conjugate divides their sum 2. Since `f` is even, it also divides `z−2(f/2)√11=1`. Unique factorization now gives `z` as a unit times a cube. The fundamental unit is `ε=10+3√11`. Absorbing the sign and any cube of a unit leaves `z=εⁱ(a+b√11)³` with `i=0,1,2`. [Norm-Euclidean ring and unit group](HosoyaRealEleven.lean)

Since `9 ∣ f`, the coordinates of `z` modulo 9 are `(1,0)`. For each of the nontrivial unit classes, `ε=(10,3)` and `ε²=(199,60)`, testing the 81 possible residue pairs `(a,b)` rules out these coordinates. In the remaining class the real coordinate reads `a(a²+33b²)=1`, forcing `a=1,b=0`. The imaginary coordinate gives `f=0`, and the original equation gives `y=−1`. [Kernel-checked descent](HosoyaProductCubeDescent.lean)

## Passing to the Fibonacci product

The Fibonacci pair repeats after 48 steps modulo 252. Among the 48 index residues, only 0, 12, 24 and 36 survive both cubic congruences `y³+1 ≡ 11Fₙ²` modulo 28 and modulo 9. Each has `18 ∣ Fₙ`, so the descent rules out a nonnegative cube root at every index.

At even indices the neighboring product is `11Fₙ²−1`. At odd indices from three onward, the product is 3 or 5 modulo 7, neither a cube. The index-one product is 12. The main Lean declaration uses `n=m+2`, matching the earlier product identity. The separate Bennett–Skinner input handles the higher odd exponents in the proper-power conclusion. [Product identity](NeighboringPrimePairs.md) · [Existing square and odd-index tests](HosoyaNeighborProductPowers.lean) · [Bennett and Skinner, Theorem 1.1](https://doi.org/10.4153/CJM-2004-002-2)

The declarations are `HosoyaCubeNorm.cube_norm_at_eighteen`, `fib_cube_add_one_ne_eleven_square`, `neighboring_product_ne_cube_unconditional`, and `neighboring_product_ne_power_of_fermat_eleven` in namespace `Arxiv.«2211.10788»`. The last one takes `BennettSkinnerEleven` as an explicit argument. The pinned conjecture on infinitely many prime upper values and the simultaneous prime-values question remain open. Codex assisted with the formalization. [Pinned source](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/8156) · [Notebook replay](../../README.md#replay)
