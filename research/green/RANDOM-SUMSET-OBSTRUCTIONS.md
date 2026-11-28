# A coefficient of at least 10/9 for tenfold sums

**Every universal coefficient in Green 50 is at least $10/9$.** For every integer $r\ge2$, the corresponding assertion for $r$ summands would require $C\ge r/(r-1)$. This is a necessary condition. The existence of any finite universal coefficient in the tenfold case remains open. [Lean declarations](Green50RandomImages.lean) · [Pinned Green 50](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/50.lean)

For any fixed positive integer $b$, take ambient dimension $n=(rb+1)s$. For **every sufficiently large** $s$ there exists a set $A$ of exactly $2^{bs}$ points such that every affine flat in $rA$ has dimension less than a constant $k=k(r,b)$. The density is $2^{-((r-1)b+1)s}$. Letting $s$ grow gives
$$
C\ge\frac{rb+1}{(r-1)b+1}.
$$
Letting $b$ grow gives the stated bound. The earlier explicit BCH family gives $20/19$ for ten summands, with flat dimension at most ten at every scale. [Explicit construction](SPARSE-SUMSET-OBSTRUCTIONS.md)

## Why a random image works

Choose a linear map $P:\mathbb F_2^M\to\mathbb F_2^n$ uniformly from the finite set of all such maps. Use the image of the radius-one Hamming ball as candidate generators. An $r$-term sum then lifts to a vector of weight at most $r$.

If a fixed $k$-flat is covered, its $2^k$ distinct points have distinct short lifts. When $2^k>(rt+1)^r$, these lifts contain $t$ linearly independent vectors. Indeed, fewer than $t$ chosen lifts use at most $rt$ coordinates in total. All vectors of weight at most $r$ supported on those coordinates are sums of $r$ letters from an alphabet of size at most $rt+1$, counting zero as a letter. So at least one new lift uses a fresh coordinate.

For a prescribed independent tuple, its $t$ images are jointly uniform. Prescribing their values is always possible by extending a linear map, and each assignment admits the same number of extensions. Thus the fraction of maps sending all of them into any one $k$-flat is $2^{-(n-k)t}$. There are at most $(M+1)^{rt}$ short tuples and at most $2^{n(k+1)}$ affine parametrizations. Multiplying gives the first bound on the fraction of bad maps.

A second use of the same count with singleton targets and radius one guarantees that each image has at most three preimages in the radius-one ball. Taking $M+1=2^{bs+2}$ leaves enough distinct images to select exactly $2^{bs}$ generators. The Lean proof chooses $k,t$ first and checks that the two bad fractions sum to less than one for all sufficiently large $s$. Passing to a subset preserves the exclusion of $k$-flats. [Finite counting criterion and parameter choices](Green50RandomImages.lean) · [Replay instructions](../README.md#replay)
