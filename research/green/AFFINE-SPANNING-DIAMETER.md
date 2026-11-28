# Green 50 at high density inside the affine span

Let A be any nonempty subset of a binary vector space and let H be its affine span. If A occupies **more than 3/512 of H**, then 10A equals the direction space of H. In particular, if α is the density in the ambient cube, 10A contains a subspace of dimension at least `n − log₂(1/α)`. A family can occupy more than 3/512 of its affine span while having arbitrarily small ambient density. [Lean proof](Green50Diameter.lean) · [Pinned Green 50 statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/50.lean)

The threshold for filling the direction space is exact. In dimension 11, take zero and the eleven coordinate vectors. They span the cube and have density `12/2048 = 3/512`. Their tenfold sumset misses the all-ones vector. Green asks for a possibly smaller flat at every positive density, and that question remains open. [Green, problem 50](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#page=25)

## The general threshold

For every r ≥ 2, a family containing zero fills its linear span in r summands once its relative density exceeds `(r+2)/2^(r+1)`. Zero and the unit vectors in dimension r+1 attain the threshold and still miss the all-ones vector. Translating any family by one of its members puts zero in it. For ten summands the translation cancels in characteristic two.

Suppose a vector first appears as a sum of k ≥ 3 members. Its shortest representation defines a map from the k-cube by selecting a subset of the k summands. For each translate of A, the set of selections that land in it has Hamming diameter at most two. If two selections differed in three or more positions, their two values in the translate would replace those positions by two summands and shorten the original representation. A diameter-two subset of the k-cube has at most k+1 members. Double-counting the selections over all translates gives `2^k |A| ≤ (k+1)|G|`.

The shortest-word argument is related to Pudlák’s proof of the spanning-diameter bound in Jukna’s Theorem 17.13. The sharp fibre estimate is the diameter-two case of Kleitman’s isodiametric theorem. Klopsch and Lev study the corresponding extremal diameter problem for finite abelian groups. [Jukna, §17.5](https://web.vu.lt/mif/s.jukna/EC_Book_2nd/draft.pdf) · [Kleitman, 1966](https://www.sciencedirect.com/science/article/pii/S0021980066800273) · [Klopsch and Lev](https://arxiv.org/abs/0911.2908)

## Replay

From the notebook root, with `FC` pointing to the pinned Formal Conjectures checkout, run the notebook replay. It rebuilds the three Green 50 modules in dependency order and checks their exported proofs.

```bash
runner="$PWD/scripts/replay-research"
(cd "${FC:?set FC to the pinned Formal Conjectures checkout}" && lake env python3 "$runner")
```
