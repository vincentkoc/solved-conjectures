# Green 50 for downward-closed families

Let A be a nonempty family in the binary cube. Suppose that erasing any set of nonzero coordinates of a member gives another member. If A has density α, its tenfold sumset contains a coordinate subspace of codimension at most `log₂(1/α) · log(2)/log(999/500)`. The coefficient is about 1.00145. The theorem `green_50_downward` uses the density, iterated sumset and dimension in the pinned Green 50 statement. The conjecture for arbitrary families remains open. [Proof](Green50Downsets.lean) · [DeepMind statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/50.lean) · [Green, problem 50](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#page=25)

## Why three summands already suffice

For any base c > 1 satisfying `c^(−r) ≤ 2/c − 1`, the codimension in the r-fold sumset is at most `log_c(1/α)`. For three summands, `threefold` takes the golden ratio as the base. For ten, `999/500` satisfies the inequality by rational arithmetic. Coordinate subspaces give examples where the codimension is exactly `log₂(1/α)`.

The counting step works for different families. Given r nonempty families of densities αᵢ, `cross_union` picks one member of each so that `c^(rh) · ∏ αᵢ ≤ 1`, where h is the number of coordinates missed by their union of supports. At each coordinate, choose fibres that cover it while preserving the product of densities, or omit it and gain a factor of at least `c^r` in that product. For repeated copies of A, this gives `c^h α ≤ 1`. Assign each nonzero coordinate of a desired vector to one selected member that covers it. Downward closure permits erasing the other coordinates, so the resulting r vectors add to the desired vector.

Frankl’s bounds for families with restricted unions give the classical combinatorial estimate behind this application. Frankl and Tokushige record the polynomial `x^r − 2x + 1` and its single-family bound in equation (24), and a stronger cross-family estimate in Theorem 4.2. The Lean proof uses the coordinate induction above and then constructs the subspace inside the sumset. [Frankl, *Multiply-intersecting families*](https://doi.org/10.1016/0095-8956(91)90075-U) · [Frankl and Tokushige, §4, equation (24) and Theorem 4.2](https://www.renyi.hu/~pfrankl/F_T_Invitation.pdf#page=16)

## The optimal coefficient

For each positive integer r and each real base c > 1, the bound `codimension ≤ log_c(1/α)` holds for **every** downward-closed family exactly when `c^(−r) ≤ 2/c − 1`. If this inequality fails, Hamming balls violate the bound in arbitrarily large dimensions, even when every translate of every subspace is allowed. For c > 1 this condition is equivalent to ∑ c^(−j) ≥ 1, summed over j from 1 to r−1. The sum decreases strictly with c when r ≥ 2. For ten summands the best base lies between 1.998029 and 1.998030, giving an optimal base-two coefficient of about 1.001424. Every coefficient that works for unrestricted Green 50 must satisfy the same lower bound. For two summands no finite coefficient works. [Sharpness proof](Green50Sharp.lean)

To see why balls detect the constant, pick a maximum-weight vector in an affine flat. Projection onto its support is injective on the direction space. Any nonzero kernel vector would add support outside the chosen vector and increase its weight. It follows that every flat in an r-fold sum of radius-k balls has dimension at most rk.

Write `B(n,k)` for the radius-k ball. If the proposed bound works on these balls, then `|B(n,k)| cⁿ ≤ 2ⁿ c^(rk)`. Weight level k by `t^k` with `t = c^(−r)`. Summing over the n+1 levels gives `(1+t)ⁿ ≤ (n+1)(2/c)ⁿ` by the weight enumerator of the cube. Exponential growth now forces `1+t ≤ 2/c`. The argument still applies after discarding finitely many dimensions. For n > rk, these balls are instances of the Daykin families in the combinatorial literature. [Frankl and Tokushige, Definition 4.2](https://www.renyi.hu/~pfrankl/F_T_Invitation.pdf#page=15)

The same pinned notebook runner rebuilds the downset proof and its sharpness converse. [Replay command](AFFINE-SPANNING-DIAMETER.md#replay)
