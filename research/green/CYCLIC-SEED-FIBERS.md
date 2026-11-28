# Green 33 · energy bounds from the sizes of quotient fibers

For a strict two-sum cover of a cyclic group of order `N` by `k` labels, **2N ≤ k² − 2k + 4**. When doubling is injective, the constant is **3**. The strict covers `{0,1,2,4}` modulo 6 and `{0,1,2,3,6}` modulo 9 give equality in the respective bounds. The proof gives a stronger test when the sizes of the fibers of a quotient are known. It rules out 17 labels modulo 117 split into one singleton and eight doubletons modulo 9. [Lean proof](Green33CyclicSeedFibers.lean)

## Projected representation counts

Let the ambient group be `H × K`, with `|H|=p`, `|K|=q` and `N=pq`. Write `a_i` for the number of labels above `i∈H`. In row `r`, the number of ordered pairs and the number of diagonal pairs are respectively

```text
Tᵣ = Σᵢ aᵢ aᵣ₋ᵢ,        Dᵣ = Σ₂ᵢ₌ᵣ aᵢ.
```

For strict coverage, each target needs two ordered witnesses in addition to its diagonal pairs. Hence `Vᵣ = Tᵣ − Dᵣ − 2q` is nonnegative. For ordinary coverage, a diagonal pair suffices on its own, so the corresponding doubled unordered excess is `Uᵣ = Tᵣ + Dᵣ − 2q`. If doubling is injective on the group, the row totals satisfy

```text
Σᵣ Vᵣ² ≥ 2N − 4k + 6                   (strict coverage)
Σᵣ Uᵣ² ≥ 2k² − 2N − 6k + 6             (ordinary coverage).
```

The second assertion uses the sumset equality `A + A = univ` from the pinned Green 33. Its additional hypotheses are a displayed product decomposition and injective doubling. Green asks for infinitely many positive cyclic orders with normalized size arbitrarily close to √2. These inequalities give finite necessary conditions. [Pinned conjecture](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Strict-seed equivalence](STRICT-REDUCTION.md)

## Uniform fibers and the order-117 test

If each quotient fiber has `h` labels and doubling is injective, then each strict excess equals `ph²−h−2q`. The theorem `uniform_fibers` gives

```text
(ph² − h − 2q)² ≥ 2q − 4h + 1.
```

In particular a growing sequence of these covers with fixed `h` needs a row excess of order at least √q. With a single label per fiber, a graph over an odd-order group can cover strictly only if `p ≥ 2q+1+√(2q−3)` for `q≥2`.

For 17 labels modulo 117 with one singleton and eight doubletons modulo 9, the singleton can have any residue `c`. The strict row excess is 6 in row `2c` and 4 in each of the other eight rows. Their squared sum is 164. Strict coverage requires `2·117−4·17+6=172`. The theorem `cyclic_117` uses the natural representatives modulo 9 of the original labels in `ZMod 117`. Other size-17 profiles are outside this certificate. [Lean proof](Green33CyclicSeedFibers.lean)

## Proof of the energy test

Let `R` and `L` be ordered sum and difference counts, respectively. Their first and second moments agree. For `P(x)=(x−2)(x−3)`, this gives `Σ P(R) = Σ P(L) ≥ P(k)`, since `L(0)=k` and `P` is nonnegative on integers. In the strict case write `R=2+d+w`, where `d` counts diagonal pairs and `w≥0`. Injective doubling gives `d≤1`, hence `P(R)≤w²+w`. Summing, using `Σw = k²−k−2N`, and grouping by quotient row proves the strict estimate. In the ordinary case write `w=R+d−2`. Then `P(R)≤w²−w+2d`, giving the second estimate. In a cyclic group each target has at most two diagonal witnesses, and the weaker strict bound `P(R)≤w²+3w+d` gives the constant 4. [Sum and difference moments](Green33TailEnergy.lean) · [Earlier ordinary order bound](REFLECTION-RIGIDITY.md) · [Li and Chen, Lemma 2.1](https://doi.org/10.1017/S0004972717000302)

Graham and Sloane's maximal strict order and Haanpää's finite census concern the same distinct-summand convention. The results here are Lean certificates. The cyclic seed with the best coefficient in this notebook still has 18 labels modulo 130. Codex assisted with the formalization. [Graham–Sloane, §§1 and 15](https://mathweb.ucsd.edu/~ronspubs/80_07_harmonious.pdf) · [Haanpää, §5](https://cs.uwaterloo.ca/journals/JIS/VOL7/Haanpaa/haanpaa.pdf) · [Order-130 construction and attribution](QUARTIC-SEED.md) · [Notebook replay](../README.md#replay)

The independent Lean 4.33.1 replay compiles the five notebook dependencies and this module from source. All ten theorems print only `propext`, `Classical.choice` and `Quot.sound`. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33)
