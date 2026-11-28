# Complementary constants restrict Jones factor degrees

Let `Pⱼ(X) = Xʲ + ⋯ + X + m`, where `m = 2(2ᵗ+1)/3`. For every odd `t ≥ 5`, a monic integral factor with constant 2 forces

```text
j ≡ t  (mod t(t+1)).
```

If the odd part `(2ᵗ+1)/3` is a prime power, every reducible Pⱼ of positive degree has such a factor. Therefore **Pⱼ is reducible over ℚ exactly at j = t** throughout either of the following ranges. [Lean proof](CunninghamJonesComplementaryOrders.lean)

- `0 < j < t+t(t+1)`.
- `0 < j` and `j³·2^(2(t+1)) ≤ m³`.

The first range settles degrees 1 through 34 at `t=5`. The necessary condition beyond it is `j ≡ 5 mod 30`. The second range extends the notebook’s exponential degree bound to the prime-power odd-part hypothesis. At `t=9` the odd part is `171=3²·19`. A separate calculation confines reducibility to **9, 29, 59 and 89 modulo 90**. The other 86 classes consist entirely of irreducible polynomials in positive degrees. Reducibility in the surviving classes beyond the prescribed degree remains open in general. [Earlier degree obstruction](JonesFactorOrders.md) · [Exponential range](JonesFactorTrace.md)

## The constant term of the complementary factor

Suppose `Pⱼ=AB` over the integers with A monic of degree e, `A(0)=u` and `B(0)=v > 1`. In particular `m=uv`. Modulo v the polynomial B is divisible by X, while the identity

```text
(X−1) Pⱼ = X^(j+1) + (m−1)X − m
```

reduces to `X(Xʲ−1)`. Cancelling X gives a monic factorization of `Xʲ−1` with A as a factor. The resultant of A with `Xʲ` is `(−1)^(ej) uʲ`. It also equals 1, since `Xʲ` differs from 1 by a multiple of A. Thus

```text
(−1)^(ej) uʲ ≡ 1  (mod v).
```

In particular `u²ʲ ≡ 1 mod v`, and u and v are coprime. In a nontrivial monic factorization, both constants are positive and exceed one by the notebook’s root bound. If `m = 2q` with q a prime power, its full prime power must divide one of the two coprime constants. This leaves 2 as the other constant. [Root bound and positivity](JonesFactorOrders.md)

## Combining the two orders

Write `q=(2ᵗ+1)/3` and `M=2q−1`. For a constant-two factor the earlier congruence gives `2^(j+1) ≡ 1 mod M`. The complementary congruence gives `4ʲ ≡ 1 mod q`. The order of 2 modulo M is `t+1`, and the order of 4 modulo q is t. These order identities require no primality assumption on q.

For the second identity, `2ᵗ ≡ −1 mod q`, so the order e of 4 divides t. A proper divisor e of the odd integer t satisfies `3e ≤ t`. Then `q+1 ≤ 4ᵉ` would imply `(q+1)³ ≤ 4ᵗ = (3q−1)²`, impossible since `q ≥ 11`. For the first identity a proper order e would satisfy `2e ≤ t+1`, forcing `(M+1)² ≤ 2^(t+1)=3M+1`. Hence `t ∣ j` and `t+1 ∣ j+1`. Consecutive moduli are coprime, giving the degree class above.

At `t=9` the coprime constant splits with the smaller constant first are `2·171`, `9·38` and `18·19`. The first gives `j ≡ 9 mod 90`. For the second, the order of 9 modulo 341 is 15 and the order of 81 modulo 38 is 9. This would force both `3 ∣ j+1` and `3 ∣ j`. For the third, 18 has order 30 modulo 341, so `30 ∣ j+1`. Lean checks all three orders by modular exponentiation.

## Scope and replay

Jones’s Conjecture 4.1 sets `t=2⌈(k+1)/2⌉+1` and asks for the reducibility classification for every `j ≥ t−k`. The conclusions here are degree restrictions and partial ranges. The pinned DeepMind declarations concern infinitely many integer prime seeds of each exact chain length for the two signs. Both declarations remain open. [Jones, p. 7](https://arxiv.org/pdf/1104.1579#page=7) · [Pinned DeepMind declarations](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean)

Lean 4.33.1 compiled the pinned source and five notebook modules from fresh output. Separate kernel replays passed for all five. All 22 named axiom reports use only `propext`, `Classical.choice` and `Quot.sound`. The five result declarations are `jones_factor_complementary_modulus`, `jones_constant_two_degree_class`, `jones_prime_power_part_degree_class`, `jones_prime_power_part_range` and `jones_nine_complementary_classes`. [Notebook replay](../../README.md#replay)
