# A coefficient of at least 20/19 for Green's tenfold bound

For every positive $m$ there is a set of exactly $2^m$ points in the binary cube of dimension $20m$ such that **every affine subspace in its tenfold sum has dimension at most ten**. Its density is $2^{-19m}$. A coefficient $C$ valid for every set in Green 50 would have to satisfy $20m-19mC\le10$ for every $m$. Thus $C\ge20/19$. The same construction with $r$ summands gives $(2r-1)C\ge2r$ under the corresponding universal bound. The existence of an absolute coefficient for ten sums remains open. [Lean proof](Green50BCH.lean) · [Pinned Green 50](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/50.lean)

## The construction

Take $K=\mathbb F_{2^m}$ and use zero together with the columns
$$
(x,x^3,\ldots,x^{4r-1})\in K^{2r},\qquad x\in K^\times.
$$
These are parity checks from a classical binary BCH code. Any nonempty sum of at most $4r$ distinct columns is nonzero. Indeed, if the odd power sums vanished, squaring would give every power sum of exponents $1,\ldots,4r$. For $s$ distinct nonzero inputs the first $s$ equations give an invertible Vandermonde matrix times a vector of nonzero inputs, a contradiction. [Bose and Ray-Chaudhuri, 1960](https://doi.org/10.1016/S0019-9958(60)90287-4) · [Mathlib's Vandermonde identity](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Vandermonde.lean)

A point in $rA$ is the image of a binary coefficient vector of Hamming weight at most $r$. Suppose an affine subspace lies in $rA$. Choose one short representative for each of its points. In any parallelogram their four representatives sum to a kernel vector of weight at most $4r$, so their sum is zero. Subtracting the representative of a basepoint gives an injective linear lift of the direction space. The original affine space thus lifts into the radius-$r$ Hamming ball, which contains no affine subspace of dimension greater than $r$. [Flat-lifting argument](Green50BCH.lean) · [Weight bound](Green50Sharp.lean) · [Replay instructions](../README.md#replay)

For downward-closed families the optimal tenfold coefficient is about $1.001424$. The explicit sets here require a larger coefficient when all sets are allowed. [Downward-closed theorem](POLYNOMIAL-BOGOLYUBOV.md)
