# Green 33 · approximate cyclic sum covers

Green 33 is equivalent to finding cyclic sets of size `(√2+o(1))√M` that cover all but `o(M)` residues by two-element sums. The moduli tend to infinity. The same criterion works when every representation must use distinct elements, or when the defect counts excess unordered representations. An approximate seed can yield a full basis at a **different** modulus. The existence of such a sequence remains open. [Lean proof](Green33ApproximateCovers.lean) · [Green, Problem 33](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#page=18) · [Pinned DeepMind declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

## A certificate from one finite set

Let `A ⊆ Z/M` have `k` elements, and let `e` count the residues missing from sums of **distinct** elements. Write `S` for the common limiting maximal order divided by the square of the size budget for ordinary and strict cyclic covers. Then `finite_certificate` gives

```text
M ≤ S (k + 2√e)².
```

The ratios `M/(k+2√e)²` over all finite seeds have supremum exactly `S`. At `e=0` this recovers the strict seed ratio `M/k²`, whose supremum is already `S`. The coefficient 2 comes from the digit construction below. Its optimality among all repairs is open here. [Maximal orders and the definition of S](MAXIMAL-ORDERS.md)

For widths `Q = sℓ+1`, with `s = k! M`, the Chinese remainder theorem identifies the lifted group with `Z/Q² × Z/M`. Put a progression of length `s+Q` at each seed label. Two different labels fill the entire layer over their sum. To cover the other layers, take `L=⌊Q√e⌋+1` low digits at label zero and multiples of `L` below or equal to `Q²` at each missing label. Euclidean division represents every coordinate. The repair uses at most `2Q√e+e+1` elements. Thus `approximate_lifts` produces a complete ordinary cyclic basis modulo `MQ²` with size at most `(k+2√e)Q+ks+e+1`. Divide by the width and use the maximal-order limit. [Progression-pair lemma](STRICT-COVER-LIFT.md)

## Missing residues and excess pairs

For each occupied residue with `t` unordered representations, charge `t−1`. Their sum is the excess `D`, and `H` denotes the number of holes. Double summands contribute once in the ordinary convention. The exact identities in `pair_balances` are

| Convention | Total unordered pairs | Balance |
| --- | --- | --- |
| Distinct elements | `k(k−1)/2` | `D−H = k(k−1)/2−M` |
| Diagonals allowed | `k(k+1)/2` | `D−H = k(k+1)/2−M` |

At the proposed size, dividing either balance by `M` gives a difference tending to zero. The two hole counts differ by at most `k=o(M)`. These comparisons hold on the same sequence of seeds. Excess measures linear mass above one, so a residue with large multiplicity can still make a substantial contribution to quadratic energy. [Hereditary energy bound](HEREDITARY-TAIL.md)

Erdős and Freud call an integer set quasi-Sidon when its pair sums take asymptotically as many distinct values as there are unordered pairs. Here the excess condition makes the cyclic seeds quasi-Sidon in that sense, with sums taken modulo the ambient order. Their interval problem has a different ambient set and requires care when passing between the two sumsets. [Erdős–Freud](https://www.sciencedirect.com/science/article/pii/0022314X9190083N)

The building blocks are the notebook’s strict-seed lift and the Graham–Sloane order limit. Haanpää studies exact finite ordinary and strict covers. Bevan, Erskine and Lewis construct large circulants with prescribed diameter. Xu and Zhou study lattice packings by Lee spheres at density `|S(n,r)|/(|S(n,r)|+1)`, with disjoint spheres. These comparisons do not establish priority for the approximate-cover criterion. [Haanpää](https://cs.uwaterloo.ca/journals/JIS/VOL7/Haanpaa/haanpaa.html) · [Bevan–Erskine–Lewis](https://arxiv.org/abs/1506.04962) · [Xu–Zhou](https://arxiv.org/abs/2210.03361)

The statements `green_iff_approximate` and `green_iff_pairExcess` use the pinned Green 33 predicate on the left, including its absolute error and frequent positive moduli. Both conventions are available through the Boolean argument. All twelve public theorems print only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the proofs. [Replay instructions](../README.md#replay)
