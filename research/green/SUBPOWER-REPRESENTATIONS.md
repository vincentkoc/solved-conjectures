# Green 33 · subpower ordered representation counts

Assume Green 33. There is a single family of strict cyclic two-bases with orders `N_t` tending to infinity and sizes `|B_t|/√N_t → √2` whose largest ordered sum count tends to infinity, yet eventually satisfies `maxReps(B_t)^h ≤ N_t` for every fixed positive integer `h`. The divergence holds for every asymptotically optimal family. The upper bound comes from constructing a family. [Lean proof](Green33SubpowerRepresentations.lean) · [Divergence theorem](DIVERGENCE.md)

The unconditional construction starts with any strict cyclic seed of size `k` and order `M`. There is a constant `C>0`, depending only on that seed, such that for every ε > 0 arbitrarily large cyclic orders `N` have a strict basis `B` satisfying both

```text
|B| / √N < k / √M + ε
maxReps(B) ≤ exp(C √(log N)).
```

Here a strict basis represents every residue with two distinct points. The peak counts **all ordered pairs** of points with a given sum, including equal summands. The constant in the exponential may change when the seed changes. The construction supplies arbitrarily large orders. [Definitions and proof](Green33SubpowerRepresentations.lean)

## The finite construction

Put `s = k!`. Take a prime `q > max(2,s)` congruent to 1 modulo `s` and any dimension `d`. The theorem `finite_lift` gives a strict basis at order `N = M(q²)^d` with

```text
|B| ≤ k(q+s)^d
maxReps(B) ≤ k² [16(4k+7)]^d (q+s).
```

Number the seed labels from 0 to `k−1`. The arm for label `i` consists of that label plus `M` times a sum of blocks with place values (`q²`^j). For parameters `0≤t_j<q+s` the block at place `j` is `(s+iq)t_j + q(t_{j−1}² mod q)`, with previous parameter zero at the first place. Any two distinct arms cover every residue above their label sum. After solving one place by the two-progression lemma, the previous parameters and the carry only translate the next target. [Two-progression lemma](STRICT-COVER-LIFT.md) · [Twisted pair proof](Green33SubpowerRepresentations.lean)

To count a fiber, fix its target and its ordered labels. Record the quotient of each raw block sum by `q²`, the quotient of `t_j+u_j` by `q`, the quotient of `t_j` by `q`, and the order of the two parameter residues modulo `q`. There are at most `16(4k+7)` choices per place. Also record the final first-arm parameter. These data recover both words. The raw quotients and target determine all block sums by successive division. Reduction modulo `q` and the recorded quotient then recover `t_j+u_j`. Unequal slopes determine the two parameters separately. For equal slopes, the next block gives the sum of the two preceding squares modulo `q`. Over an odd prime field, the sum and sum of squares determine an unordered pair. Its order bit and first quotient recover the ordered pair. At the last place the recorded parameter suffices. Choosing one parameter word for each actual basis point makes the same bound apply when an arm has repeated encodings. [Fiber count](Green33SubpowerRepresentations.lean)

Choose `d = ⌊log q⌋` along primes congruent to 1 modulo `s`. The factor `(1+s/q)^d` tends to 1. The logarithm of the peak bound grows at most linearly in `log q`, and `√(log N) ≥ log q` for these choices once `q` is sufficiently large. This gives `seed_sqrt_log`. The theorem `ordinary_iff_subpower` applies the finite strict-seed criterion and obtains an equivalence with the pinned ordinary Green 33 statement. Finally `subpower_family` chooses one sequence with shrinking tolerances and increasing exponents. Existence at the √2 endpoint remains conditional. [Finite strict criterion](STRICT-REDUCTION.md) · [Pinned Green 33 declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

## Related work and verification

Ruzsa's work already gives cyclic bases with bounded representation counts for every modulus. Sándor and Yang describe that result and study the minimum possible peak. The theorem here controls the peak while retaining an arbitrary strict seed's normalized size to any prescribed tolerance. Searches of the DeepMind tracker, Left to Solve and Open Math Agents found no matching formal declaration. [Sándor and Yang, §1](https://doi.org/10.4064/aa161227-27-4) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33) · [Open Math Agents search](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues?q=%22Green33%22+%22subpower%22)

The five local modules in the import closure were compiled from clean sources and independently replayed with Lean 4.33.1. All seven exported theorems in the new module print only `propext`, `Classical.choice` and `Quot.sound`. [Lean source and axiom checks](Green33SubpowerRepresentations.lean)
