# Frobenius inversion and Jones polynomial degrees

For Jones’s fourth parameter, every positive divisor j of `19^h + 1`, for any positive h, gives an irreducible polynomial over ℚ of the following form.

```text
Pⱼ(X) = 342 + X + ⋯ + Xʲ.
```

In particular, this holds for every degree `13^a · 29^b` with natural a and b. The first, third and fifth powers of 29 are respectively 29, 89 and 59 modulo 90. Since `29⁶ ≡ 1 (mod 90)`, odd powers visit each of these classes infinitely often. All three classes survived the complementary-order test. The degree 59 itself is outside the inversion criterion because 19 has order 29 modulo 59. [Lean application](CunninghamJonesFrobeniusDegrees.lean) · [Complementary-order test](JonesComplementaryOrders.md)

Jones’s Conjecture 4.1 sets `t = 2⌈(k+1)/2⌉+1` and `m = 2(2ᵗ+1)/3`. Both k = 6 and k = 7 give t = 9 and m = 342. The claimed exception j = 9 has root −2. The criterion here leaves other degrees to be decided. The pinned DeepMind questions ask whether there are infinitely many natural prime seeds of each exact length under the two integer recurrences. Both remain open. [Jones, Conjecture 4.1](https://arxiv.org/pdf/1104.1579#page=7) · [Pinned integer-chain predicates and hypotheses](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean) · [Earlier eventual irreducibility bound](JonesLargeDegree.md)

## Why factor constants matter

Let p be prime. Over the field with p elements, suppose a monic polynomial A divides `X^(p^h+1)−1` and `A(1) ≠ 0`. Then `A(0) = 1`. To see this, let x be the class of X modulo A. The equation `x^(p^h+1) = 1` gives `x^(p^h) = x⁻¹`. Raising `A(x)=0` to the power `p^h` fixes the coefficients and gives `A(x⁻¹)=0`. Thus A divides its reverse. The reverse has degree at most that of A, so it is a scalar multiple of A. Evaluating at 1 makes the scalar 1. Comparing constant terms gives `A(0)=1`, since the constant of the reverse is the leading coefficient of A. The argument takes place in the quotient by the entire factor. [Finite-field proof](CunninghamJonesFrobeniusFactors.lean)

Now let m ≥ 3, p divide m, and j divide `p^h+1` for h > 0. Suppose `Pⱼ=AB` is a nontrivial monic integral factorization. The root bound gives both constants greater than 1. Choose the order so p divides `B(0)`. Modulo p, B loses a factor X. The identity `(X−1)Pⱼ = X(Xʲ−1)` then shows that A divides `Xʲ−1`, and hence `X^(p^h+1)−1`. Also `Pⱼ(1) ≡ j ≠ 0 (mod p)`. The finite-field lemma forces `A(0) ≡ 1 (mod p)`. Since `A(0)` divides m/p, **irreducibility follows whenever m/p has no divisor greater than 1 congruent to 1 modulo p**. At m = 342 and p = 19, the complementary bound is 18. [General criterion](CunninghamJonesFrobeniusDegrees.lean) · [Root bound](JonesLargeDegree.md)

## Lifting one inversion to mixed degrees

Suppose d is odd and divides `a+1`. Put `v = (−a)^(d^r)`. Modulo d, v equals 1, so `1+v+⋯+v^(d−1)` is divisible by d. The geometric sum identity lifts `d^r ∣ v−1` to `d^(r+1) ∣ v^d−1`. Since every `d^r` is odd, this proves `d^r ∣ a^(d^r)+1` for all r. At `d = 377 = 13·29`, direct modular exponentiation gives `19^42 ≡ −1 (mod 377)`. Every mixed degree in the stated family divides a power of 377. Moree studies the integers dividing a sum of equal powers, including this inversion condition with one base equal to 1. [Lean degree family](CunninghamJonesFrobeniusDegrees.lean) · [Moree, *On the divisors of aᵏ+bᵏ*](https://matwbn.icm.edu.pl/ksiazki/aa/aa80/aa8031.pdf)

Lean 4.33.1 rebuilt five notebook modules and independently kernel-replayed each one. The 20 named axiom reports contain only standard axioms from `propext`, `Classical.choice` and `Quot.sound`. Independent finite-field arithmetic enumerated 1,874 monic polynomial cases over the fields of sizes 2, 3 and 5 and checked all 22 divisors passing the hypotheses. It also checked the inversion for all 25 mixed degrees with 0 ≤ a,b ≤ 4. [Notebook replay](../../README.md#replay)
