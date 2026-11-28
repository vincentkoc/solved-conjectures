# Growth of the stable affine class count

Let $N(h)$ count affine classes of dense binary doubles with $h$ unused sites in the Green 51 carrier. Once the number of rows is at least $h$, the fibre dimension is at least $h-1$, and each fibre has more than $h$ sites, this count depends only on $h$. In this range
$$
\lim_{h\to\infty}\frac{\log_2 N(h)}{h^2}=\frac14.
$$
The limit holds for every sequence of admissible ambient dimensions. Here the carrier has $2s+3$ rows with $s\ge5$, the ambient dimension is $2s+2+r$, and the doubles and density threshold are those of the [stable class theorem](STABLE-FIBRE-AND-ROW-DIMENSIONS.md). [Limit for the actual sumset classes](Green51UniversalQuadraticRate.lean)

### Finite bounds

Write $u=\lfloor h^2/4\rfloor$. For every $h\ge10$ the following integer inequalities hold.
$$
2^u\le N(h)\,h^h\,2^{h+\lfloor h/2\rfloor},
\qquad
N(h)\le h^h(h+1)\,2^{u+h}.
$$
The upper inequality also holds for $0\le h<10$. In natural logarithms the proof gives $|\log N(h)-h^2\log(2)/4|\le h\log(h)+4h$ for $h\ge10$. [Integer bounds](Green51DefectGrowthBounds.lean) · [Logarithmic error](Green51UniversalQuadraticRate.lean)

For the lower bound, put all $h$ marked sites in one row of dimension $d$. Enlarging the fibre preserves inequivalence. Each affine orbit in that row has at most $2^{d^2+d}$ members, since the images of a linear basis and the shift determine the map. Thus $\binom{2^d}{h}\le N(h)2^{d^2+d}$ whenever $h>0$ and $d\le h-1$. Take $d=\lfloor h/2\rfloor$. [Single-row lower bound](Green51SingleRowGrowth.lean)

For the upper bound, label the $h$ sites of a representative. Record its row assignments and the kernel of the linear combination map on its $h$ site vectors. Equal records imply a common invertible linear change of coordinates that matches all rows. There are $h^h$ possible row assignments. Counting ordered bases bounds the number of subspaces of binary $h$-space by $(h+1)2^{u+h}$. [Encoding](Green51LabelledKernelBound.lean) · [Subspace count](Green51SubspaceGrowth.lean)

The exponent $1/4$ is classical in enumerating binary subspaces, codes and matroids. Wild obtained a sharper asymptotic for ordinary binary codes up to coordinate permutation. The result here transfers the quadratic exponent to Green's affine sumset classes with independent row translations. The general guaranteed-dimension conjecture remains open. [Marcel Wild, *The asymptotic number of binary codes and binary matroids*](https://arxiv.org/abs/cs/0408011) · [Pinned Green 51 problem](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

From the pinned Formal Conjectures checkout, run `lake env python3 "$runner" Green51UniversalQuadraticRate` using the [notebook replay setup](../README.md#replay).
