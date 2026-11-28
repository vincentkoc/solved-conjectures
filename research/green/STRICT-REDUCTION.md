# Green 33 · distinct summands and the finite infimum

Green asks whether arbitrarily large cyclic groups admit two-bases of size `(√2 + o(1))√N`. The answer is unchanged if every residue must be the sum of two **distinct** basis elements. Equivalently, Green 33 holds exactly when the infimum of `|S|/√N` over all finite cyclic strict sum covers is `√2`. Determining that infimum remains open. [Lean proof](Green33StrictReduction.lean) · [Green, problem 33](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#page=18) · [Pinned DeepMind statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

## The finite construction

Let `A` be a cyclic two-basis of size `k` modulo `M`. The theorem `exists_strict_lift` constructs a strict cover `B` at some modulus `N ≥ M` with

```text
|B|/√N ≤ (k + 2⌊√k⌋ + 3)/√M.
```

Index the elements of `A` as labels. Choose `s = k! M` and a sufficiently large `Q ≡ 1 (mod s)`. CRT identifies `Z/(Q²M)` with `Z/Q² × Z/M`. At label `i`, use a progression of length `Q+s` with weight `s+iQ`. Any two distinct progressions cover their full sum layer by the two-progression lemma. Their different labels guarantee distinct summands. [Progression lemma and construction](STRICT-COVER-LIFT.md)

Only the layers with labels in `E = {2a : a ∈ A}` can still need attention. Set `b = ⌊√k⌋+1` and `L = bQ`. Add the interval `[0,L)` at label zero. At each label in `E`, add the multiples `Lj` for `0 ≤ j ≤ ⌊Q/b⌋`. Each first coordinate `0 ≤ x < Q²` splits as `x mod L + L⌊x/L⌋`. Both parts are below `Q²`, and they can coincide only at zero. If both labels are also zero, use `1 + (−1)` after adding `−1` at label zero. The interval already contains `1`.

There are at most `k` exceptional layers, and `k ≤ b²`. The interval and the upper digits together cost at most `2bQ+k` elements. Choose `Q ≥ ks+k+1` to absorb the ends of the original progressions and the extra point. This gives `|B| ≤ (k+2b+1)Q` and the normalized bound above. The construction may produce a composite modulus even when the seed modulus is prime.

## Why a finite criterion suffices

Along a family with `k/√M → √2`, the overhead `(2⌊√k⌋+3)/√M` tends to zero. Conversely, any strict cover is an ordinary basis. For a strict cover of size `h`, counting unordered distinct pairs gives `2N ≤ h(h−1)`, hence `h ≥ √(2N) + 1/2`. This positive gap on bounded moduli forces finite examples within arbitrarily small tolerances to have unbounded moduli.

Graham and Sloane defined the largest modulus admitting a strict cyclic cover with a given number of labels, their function `n_γ(k)`. Haanpää tabulated small examples. The twelve-label example lifted in the notebook gives an explicit ratio limit of `√(18/7)`. The equivalence here relates the full finite optimization problem to Green’s limiting question. [Graham–Sloane, *On Additive Bases and Harmonious Graphs*, §1](https://doi.org/10.1137/0601045) · [Haanpää, *Minimum Sum and Difference Covers of Abelian Groups*](https://cs.uwaterloo.ca/journals/JIS/VOL7/Haanpaa/haanpaa.html) · [Twelve-label family](STRICT-COVER-LIFT.md)

The notebook replay recompiles the progression lemma before the reduction. The axiom reports cover the finite lift, the half-element gap, both formulations of the equivalence and the greatest-lower-bound statement. Codex assisted with the proofs. [Replay instructions](../README.md#replay)
