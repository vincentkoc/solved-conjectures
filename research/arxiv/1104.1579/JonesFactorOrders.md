# A congruence obstruction for Jones factor degrees

Let `Pⱼ(X) = Xʲ + ⋯ + X + m`, with positive degree `j`. For Jones’s odd parameter `t`, take `m = 2((2ᵗ+1)/3)`. **If the odd part of m is prime, reducibility of Pⱼ over ℚ forces t+1 to divide j+1.** In particular, at `t = 5` the only degrees still eligible for reducibility are `j ≡ 5 mod 6`. This also proves the prescribed pattern for every positive degree below `2t+1`. The exceptional degree `j=t` has root −2. Higher positive degrees in the surviving class remain open in general. [Lean proof](CunninghamJonesFactorOrders.lean) · [Linear factors](CunninghamJonesLinearFactors.lean) · [Jones, Conjecture 4.1](https://arxiv.org/pdf/1104.1579#page=7)

The criterion also applies with a composite odd part. At `t=9`, the constant is 342 and its odd part is 171. Reducibility forces `10 ∣ j+1` or `15 ∣ j+1`. This excludes 26 of the 30 residue classes modulo 30 without a bound on the degree. Both assertions are necessary conditions. The pinned DeepMind declarations concern infinitely many prime integer seeds and remain open. [Pinned Cunningham declarations](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean)

## Constant terms of factors

More generally, take any integer `m ≥ 3`. For any nonconstant monic integral factor A of Pⱼ, the positive integer `c = A(0)` satisfies

```text
c^(j+1) ≡ 1 (mod m−1).
```

Write `N = j+1`. The identity `(X−1)Pⱼ = Xᴺ + (m−1)X − m` shows that A divides `Xᴺ−1` modulo `m−1`. Over that residue ring, the resultant of A with `Xᴺ` equals its resultant with 1, since their difference is a multiple of A. The first resultant is `(−1)^(deg(A)N) cᴺ`. The second is 1 because A is monic. If N is odd, Pⱼ has no real root. It is positive on the nonnegative axis, and the trinomial in the identity is negative on the negative axis. Thus the real factor A has even degree when N is odd, so the sign is positive in every case. Monicity and the absence of nonnegative roots also give `A(0)>0`.

All complex roots of Pⱼ have absolute value greater than one, so a nonconstant monic integral factor has constant term greater than one. Gauss’s lemma now gives a finite list for any possible factorization over ℚ. Some divisor c of m must satisfy `1 < c`, `c² ≤ m` and the congruence above. Taking the smaller constant term in a monic factorization proves the square bound. [Root bound](CunninghamJonesLargeDegree.lean)

If `m=2q` with q prime, one factor has constant term 2. Write `M=m−1`. At a Jones parameter, `2^(t+1)=3M+1`, so the order of 2 modulo M divides `t+1`. If that order were a proper divisor e, then `2e ≤ t+1` and `M+1 ≤ 2ᵉ`. Squaring would give `(M+1)² ≤ 3M+1`, impossible for M > 1. The order is therefore exactly `t+1`.

For `m=342`, the possible smaller constants are 2, 3, 6, 9 and 18. Modulo 341 they all have thirtieth power 1. A finite check of the 30 possible exponent residues leaves only 0, 10, 15 and 20. The same constant-term test applies to arbitrary m without factoring a polynomial of degree j.

The notebook's separate [finite degree bound](JonesLargeDegree.md) excludes all sufficiently large degrees at a fixed constant and settles every degree at `t=3`. The congruence here excludes entire classes of degrees uniformly across the prime-odd-part family.

Lean 4.33.1 compiled the pinned source and three notebook modules from fresh output. Separate kernel replays passed for all three. All twelve named axiom reports use only `propext`, `Classical.choice` and `Quot.sound`. [Notebook replay](../../README.md#replay)
