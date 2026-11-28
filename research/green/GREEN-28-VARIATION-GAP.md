# Green 28 as a total variation bound

A positive answer to Green 28 is equivalent to the following estimate. There is a single $\delta>0$ such that whenever two independent integer laws have a sum uniform on its support, **at least one** marginal has total variation distance at most $1-\delta$ from the uniform law on its own support. The choice of marginal may vary with the example. The same $\delta$ must work for all finite supports. [Equivalence in Lean](Green28Variation.lean) · [Pinned Green 28](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/28.lean)

More precisely, if Green 28 fails, for every $\varepsilon>0$ there are independent inputs with **both** distances greater than $1-\varepsilon$ and with an exactly uniform sum. They can have the same multiset of atom probabilities. In fact, the second law is always the image of the first under the same integer permutation $\tau$. This is a conditional consequence. The proof supplies neither a counterexample nor a value of $\delta$ for the unrestricted problem. [Far-marginals theorem](Green28Variation.lean) · [Fixed digit permutation](GREEN-28-DIGIT-TRANSPOSE.md)

## Why a fixed gap would suffice

For a law $P$ with nonempty finite support $A$, let $u=1/|A|$. The proof uses total variation and the Bhattacharyya affinity with the uniform law,
\[
  V(P,A)=\tfrac12\sum_{x\in A}|P(x)-u|,\qquad
  a(P,A)=\sum_{x\in A}\sqrt{P(x)u}.
\]
The arithmetic-geometric mean inequality gives $a(P,A)<1$ if $P$ is nonuniform. The pointwise inequality $(\sqrt p-\sqrt u)^2\le |p-u|$ gives $1-a(P,A)\le V(P,A)$. Both quantities are invariant under injective relabelling of the support. Affinity multiplies under independent products. These product and distance identities are standard. [Polyanskiy and Wu, §7.3](https://people.lids.mit.edu/yp/homepage/data/itbook-export.pdf) · [Finite-sum proofs](Green28Variation.lean)

Apply the fixed-permutation construction to any counterexample. It yields a nonuniform law $R$, its relabelled copy, and an exactly uniform sum. Apply the construction again to this pair. The new marginal is an injectively labelled product of the two inputs, so its affinity is the square of the previous value. The uniform-sum condition survives each step. After $n$ steps the affinity is $a^{2^n}$ with $0\le a<1$. Both variation distances are therefore at least $1-a^{2^n}$. Conversely, if Green 28 holds, both distances vanish and $\delta=1$ works. [Construction and iteration](Green28Variation.lean)

## Source comparison and replay

The proof uses the type of the pinned Green 28 declaration directly and imports the previously checked product construction. The uniformity hypothesis always refers to the actual independent sum law. The searches of DeepMind, Left to Solve, Open Math Agents and the unfair-dice literature found polynomial cases and finite tests, including the OMA prefix comparison. They did not locate the total variation equivalence above. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1563) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/2380) · [Left to Solve](https://lefttosolve.com/api/problems/Green28.green_28) · [OMA polynomial comparison](https://github.com/lefttosolve2/open-math-agents/pull/21793) · [Ghidelli](https://arxiv.org/abs/2209.09843)

Lean 4.33.1 rebuilt the pinned declaration and all ten notebook modules in the dependency closure from clean sources. Independent kernel replay checked each notebook module. All four printed results in the new file report exactly `propext`, `Classical.choice` and `Quot.sound`.
