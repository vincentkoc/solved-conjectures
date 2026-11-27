# Green 33 · an order-three quotient obstruction

Suppose a finite abelian group of order `q` has a two-basis `A + A = G` of size `k` attaining the [finite order bound](REFLECTION-RIGIDITY.md), so `2q = k² + 2`. If the group has a quotient of order three, **`4k − 7` is an integer square**. For a cyclic group, divisibility of `q` by 3 supplies that quotient. [Lean proof](Green33OrderThree.lean)

This excludes an infinite sequence of exact extremizers. At modulus `q = 2(15n + 5)² + 1`, every two-basis has at least `30n + 11` elements. The order bound alone gives `30n + 10`. At that candidate size the modulus is divisible by 3, but `4k − 7 = 120n + 33` is 3 modulo 5. For `n = 0` the improved lower bound is exact. The file checks Haanpää’s published 11-element basis modulo 51 against the same sumset predicate. [Haanpää, Table 3](https://cs.uwaterloo.ca/journals/JIS/VOL7/Haanpaa/haanpaa.pdf)

**Proof.** At equality the basis is invariant under a reflection `a ↦ s − a`. The ordered sum count plus the diagonal count is 2 off the center and `k` at the center. Project to the quotient via `f`. Give class 0 the integer weight 2 and the other two classes weight −1, writing `λ` for this function. Its translates sum to zero over the group. Set

```text
S = ∑_{a∈A} λ(f(a) + f(s)),
U = ∑_{a,b∈A} λ(f(a+b) − f(s)).
```

The identity `λ(x)λ(y) = λ(x+y) + λ(x−y)` and reflection in the second summand give `S² = 2U`. The diagonal contributes `S` because doubling preserves the weight on the order-three quotient. Weighting the extremal representation counts gives `U + S = 2(k − 2)`. Consequently `(S + 1)² = 4k − 7`. The proof uses integer arithmetic throughout.

**Upstream scope.** The cyclic result uses the positive moduli, `ZMod q`, and coverage equality in `Green33.green_33`. The new hypothesis is exact finite extremality. Green’s question allows a relative size error tending to zero and asks for existence on infinitely many moduli. That question remains open. [Pinned declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Green, problem 33](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.33)

**Tracker check.** The DeepMind issue and merged PR concern the statement. The LTS target listed no solution or reduction steps. Searches of the solved feed and open and closed OMA issues and PRs found no matching formalization. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [LTS target](https://lefttosolve.com/api/problems/Green33.green_33) · [LTS solved feed](https://lefttosolve.com/api/solved) · [OMA search](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues?q=%22Green33%22)

**Replay.** Use the [notebook replay command](../README.md#replay) with Lean 4.33.1. The five declarations in `Green33OrderThree` print only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the formalization.
