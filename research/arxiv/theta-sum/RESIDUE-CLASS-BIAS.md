# Opposite signs for fixed theta cones at primes

Fix an integer $J\ge2$ and an odd positive integer $K$. Let $C(p;J,K)$ be the notebook's rational nondivisible cone. It sums the reciprocal parity sign divided by $uv$ over odd $u<2J$ and odd $v<Ku$, omitting $u\mid v$. For every bound $B$ there are primes $p,q>B$ satisfying

```text
p ≡  1 (mod 24)    C(p; J, K) ≥  1/30
q ≡ 17 (mod 24)    C(q; J, K) ≤ −1/30.
```

Both progressions lie in $1\bmod 8$. The constants hold for every pair of fixed cutoffs. The result applies to the whole finite cone, including all its nondivisible pairs. [Definition and approximation](ThetaNondivisibleCone.lean) · [Prime sign theorem](ThetaConditionalRows.lean)

The two progressions also have opposite weighted prime means. Take any odd $M$ divisible by every odd denominator $3\le d\le 2J$, for example their product. Put $t_k=1/(k+1)$. For $r=1,17$ the limits

```text
lim  tₖ Σ C(p; J, K) log(p) / p^(1+tₖ)
k→∞    p prime, p ≡ r (mod 24), gcd(p,8M)=1
```

exist. The first is at least $1/30$ and the second at most $-1/30$. These are unnormalized progression means. Each progression has limiting weight $1/8$. The primes omitted by the coprimality condition divide the fixed integer $8M$. [Weighted prime limits](ThetaAbelPrimes.lean)

## Why further rows preserve the bias

Let $\chi$ be the nontrivial character modulo three. For odd $d$ divisible by three, twisting the parity of the least unit representatives gives

```text
Σ_{0≤j<d, gcd(j,d)=1} −(−1)^j χ(j) = 2 ∏_{ℓ|d, ℓ prime, ℓ≠3} (1−χ(ℓ)).
```

The substitution $u\mapsto w/u$ among units transfers this identity to the reciprocal wave with primitive numerator $w$. A prime factor $1\bmod 3$ kills the entire transform. Every remaining prime factor other than three is $5\bmod 6$. Removing multiples of such a prime $\ell$ from a reciprocal numerator sum adds $1/\ell$ times the same sum at the divided cutoff. The underlying sequence has a positive term at $6j+1$ followed by a smaller negative term at $6j+5$. This proves nonnegativity even when the numerator window stops partway through a period. [Character transform and finite prefix bounds](ThetaCharacterThree.lean)

For $d=3$ the normalized twist is at least $4/5$ at every nonempty cutoff. Denominators coprime to three have zero twist by the Chinese remainder theorem. Every untwisted row has mean zero by reflection. Consequently, any nonnegative row combination with coefficients $a(d)/d$ has full-period twisted mean at least $4a(3)/15$. Separating the two reduced classes modulo three and restricting to $1\bmod 8$ gives opposite bounds of size $a(3)/30$. The common-factor weight of the actual cone satisfies $a(3)\ge1$. Dirichlet's theorem supplies arbitrarily large prime representatives. For the weighted limits we use the pole of the progression von Mangoldt series at one and the summability of its nonprime contribution. [Finite means and CRT](ThetaConditionalRows.lean) · [Prime-weight argument](ThetaAbelPrimes.lean)

## Scope for the original sum

At odd primes, the pinned signed sum $S(p)$ equals its divisible diagonal plus an off-diagonal term. The existing estimate compares that term to $(8p/\pi^2)C(p;J,K)$ with explicit cutoff errors. Here $J,K$ are fixed before the primes tend to infinity. The subsequent [prime approximation and excursion theorem](OFF-DIAGONAL-EXCURSIONS.md) controls the discarded rows and transfers both signs to the original difference $S(p)-D(p)$ on sets of positive upper prime density. The all-prime positivity conjecture remains open. [Original conjectures, v3](https://arxiv.org/pdf/2501.03234v3#page=4) · [Pinned Lean statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean) · [Exact diagonal decomposition](ThetaDivisibleDiagonal.lean) · [Cone error bound](ThetaNondivisibleCone.lean)

The active DeepMind reduction concerns the remainder after a row decomposition. The Left to Solve entry supplies a harmonic-sum lemma. Lägeler studies distributions of individual Hardy sums. The notebook's earlier third-window result concerns rows near a rational slope. [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5611) · [LTS-listed lemma](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7126) · [Lägeler](https://arxiv.org/abs/2207.04828) · [Third-window theorem](THIRD-WINDOW.md)

The verification uses Lean 4.33.1 and the pinned upstream source in a fresh kernel replay. Codex assisted with the derivation and formalization. [Notebook replay](../../README.md)
