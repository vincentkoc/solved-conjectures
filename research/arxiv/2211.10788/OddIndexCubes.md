# Cubes on the odd Hosoya diagonals

At every positive odd index, neither `Fₙ + Lₙ₊₁` nor `Fₙ + Lₙ₋₁` is an integer cube. This also rules out prime powers whose exponent is divisible by three at these indices. The proof gives a stronger statement about the underlying binary form. For all coprime integers a and b, no integer t satisfies

```text
3a² + 2ab + 4b² = t³.
```

Primitivity matters. For example, (a,b) = (0,4) gives 64. Even-index cubes remain outside the result, and the pinned question of infinitely many upper prime values remains open. Lagarias and Weisser classified cubes in the ordinary Fibonacci and Lucas sequences, which have different initial values from the two Hosoya diagonals. [Lean proof](LucasFibonacciOddCubes.lean) · [Ching et al., introduction and §5](https://arxiv.org/abs/2211.10788) · [Pinned upper diagonal](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Lagarias and Weisser, *Fibonacci and Lucas cubes*](https://www.fq.math.ca/Scanned/19-1/lagarias.pdf)

## The cube obstruction

Put ω = (1+√−11)/2. The norm of z = x+yω is `N(z) = x²+xy+3y²`. To divide by a nonzero element, round the second coordinate of the quotient first. Round the first coordinate after adding half the second-coordinate error. For the resulting error s+rω one has `|2s+r| ≤ 1` and `|2r| ≤ 1`. Thus `N(s+rω) = ((2s+r)²+11r²)/4 ≤ 15/16`. This gives Euclidean division and unique factorization in ℤ[ω].

Suppose x,y are coprime and N(z) = t³. Any prime dividing both the trace `2x+y` and t divides `11y² = 4t³−(2x+y)²`. If that prime is 11, the right side is divisible by 121, so 11 divides y as well. In every case the norm equation then makes the prime divide x, contradicting coprimality. Consequently the trace is coprime to t³. A common divisor of z and its conjugate divides their sum and product, so it is a unit. Unique factorization makes z a cube times a unit. Every unit has zero ω-coordinate, and the ω-coordinate of `(u+vω)³` is `3uv(u+v)−2v³`, which is even. Hence y is even.

Take z = 2b+aω. Its norm is the form in the statement. If a is odd, then 2b and a are coprime, and the previous argument forces a to be even. If a is even, then b is odd and the form is 4 modulo 8, which is impossible for a cube.

## Both diagonals

Set a = Fₘ and b = Fₘ₊₁. Consecutive Fibonacci numbers are coprime. At upper index 2m+1 the Fibonacci doubling identities give the form evaluated at (a,b). The lower value at index 2m+3 gives the same form at (a+b,−b), another coprime pair. At lower index one the value 3 is the form at (1,0). The declaration for actual lower index 2m+1 uses `3F₂ₘ₊₁−F₂ₘ` throughout, including m = 0. [Neighboring diagonal definition](NeighboringLucasFibonacciPrimes.lean) · [Square values](SquareValues.md)

Lean 4.33.1 compiled the pinned source and both notebook modules in a fresh directory. Independent kernel replay passed for each module. All seven axiom reports use only `propext`, `Classical.choice` and `Quot.sound`. The declarations are `hosoya_primitive_form_ne_cube`, `odd_hosoya_diagonals_ne_cube` and `odd_lower_lucas_fibonacci_sum_ne_cube`. [Notebook replay](../../README.md#replay)
