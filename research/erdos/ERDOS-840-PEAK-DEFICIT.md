# Erdős 840 · peak multiplicity above the Sidon density

Every quasi-Sidon family in integer intervals with `|A_N|/√N → c > 1` has **maximum ordered sum count tending to infinity**. The conclusion holds for every witness at such a density and is unconditional. In particular it applies at Erdős and Freud's known lower constant `2/√3`. Under Green 33, the notebook also constructs a family at `√2` whose peak diverges but eventually lies below every fixed positive power of the interval length. [Lean proof](Erdos840PeakDeficit.lean) · [Erdős–Freud](https://www.sciencedirect.com/science/article/pii/0022314X9190083N) · [Conditional construction](../green/SUBPOWER-ALL-BUDGETS.md)

Let `k = |A|`, let `m` be the largest number of **ordered** pairs with a given sum, and let `D = binom(k+1,2) − |A+A|`. This deficit counts repetitions among **unordered** pairs, including the diagonal. For any sequence of sets of size asymptotic to `c√N` with `c > 1`, the theorem `product_lower` gives

```text
liminf mD/N ≥ (c−1)².
```

The Lean statement says that every strictly smaller real number is eventually below `mD/N`. This estimate only requires the size limit and containment in `[1,N]`. Erdős 840 adds `|A+A| ∼ binom(k,2)`, which gives `D/N → 0` because the two binomial conventions differ by exactly `k`. Applying the product bound on every sufficiently large interval forces `m → ∞`. The theorem `quasi_sidon_peak` takes the two asymptotic-equivalence clauses and the full-interval containment directly from the pinned predicate. The value of the Erdős 840 supremum remains open. [Lean proof](Erdos840PeakDeficit.lean) · [Pinned Erdős 840 predicate](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/840.lean)

## A finite inequality for translates

For every positive integer `H` and every `A ⊆ [1,N]`,

```text
H k² ≤ (N+H−1)(k+H−1+mD).
```

First write `E(A)` for the number of ordered additive quadruples. Then `E(A)+k ≤ 2k²+2mD`. For an occupied sum, let `r` and `e` count ordered representations and diagonal representations respectively. If `r=1`, the unique representation is diagonal by symmetry. If `r≥2`, use `r≤m`. In both cases `r²+2m+e ≤ (m+2)r+me`. Sum over the occupied sums, using `Σr=k²` and `Σe=k`. [Energy bound](Erdos840PeakDeficit.lean)

The mixed energy with **any** finite set of shifts `B` is at most `|B|(k+|B|−1+mD)`. To see this, write mixed energy as the scalar product of the two difference-count functions. At zero the contribution is `k|B|`. For each nonzero difference, let `x,y` be its two counts. Since `y≤|B|`, we have `2xy+|B|x ≤ 2y+|B|x²`. Summing bounds the extra mixed energy by the nontrivial quadruples already counted in `E(A)`. Taking `B={0,…,H−1}` and applying Cauchy–Schwarz to `A+B` gives the displayed window inequality. [Mixed energy and window bound](Erdos840PeakDeficit.lean)

For the asymptotic estimate, take `H=⌊(c−1)N⌋+1`. More generally a window with `H/N → t > 0` yields the lower expression `t c²/(1+t) − t` for the product divided by `N`. Its value at `t=c−1` is `(c−1)²`. [Limit argument](Erdos840PeakDeficit.lean)

## Scope and sources

The argument uses classical Sidon difference counting and translated-set Cauchy–Schwarz. Prendiville's Lemma 5.1 explicitly bounds the mass of repeated differences by the excess additive energy. O'Bryant gives the classical Sidon interval bound in Theorem 5. The statements here track the product of the peak and the unordered sum deficit for the Erdős–Freud quasi-Sidon definition. The known unconditional Erdős–Freud construction has separate Lean proofs. [Prendiville, §5](https://eprints.lancs.ac.uk/181541/1/Dense_Sidon_Sets_revision1.pdf) · [O'Bryant, Theorem 5](https://arxiv.org/pdf/math/0407117) · [Erdős–Freud formalization](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1478) · [Shorter proof](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/11577)

The DeepMind and Open Math Agents tracker searches found no matching peak-divergence theorem. The Left to Solve entry lists the original extremal problem as open. The eleven local modules in the proof's import closure were compiled from clean sources and replayed separately with the Lean 4.33.1 kernel checker. All six public theorems in the new module print only `propext`, `Classical.choice` and `Quot.sound`. [Left to Solve](https://lefttosolve.com/api/problems/Erdos840.erdos_840) · [DeepMind tracker](https://github.com/google-deepmind/formal-conjectures/issues?q=%22quasi-Sidon%22+%22bounded%22) · [Open Math Agents search](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues?q=%22quasi-Sidon%22+%22energy%22)
