# Green 54 · Gaussian convexity in a countable product

DeepMind asks whether ten sums of a balanced compact set of Gaussian mass at least 0.99 in ℝ^ℕ contain a compact convex set of mass at least 0.01. Hua, Song and Tudose proved a quantitative theorem for finite-dimensional Gaussian measure. This notebook proves the transfer to ℝ^ℕ in Lean. The finite analytic theorem is an explicit hypothesis. [Pinned DeepMind declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/54.lean) · [Lean proof](Green54GaussianProjections.lean)

## Finite projections

Let μ be any finite Borel measure on ℝ^ℕ, D a compact set, and β a mass threshold. Then D contains a compact convex set of μ-mass at least β if and only if every projection of D onto a nonempty finite coordinate set contains a compact convex set of marginal mass at least β. Each projection can choose its own witness.

For a finite coordinate set I, lift its witness back to D by taking the inverse image and intersecting with D. In the compact space of compact subsets of D, require the I-projection to be convex and its marginal mass to be at least β. Both conditions are closed. For the mass condition, outer regularity gives an open neighborhood of any compact set whose mass is below β, with neighborhood mass still below β. A witness for the union of finitely many coordinate sets meets all their conditions. Compactness gives one compact C meeting every condition. Its projection cylinders decrease to C, so continuity of the measure gives μ(C) ≥ β. Convexity follows by intersecting these convex cylinders. [`compact_convex_iff_projections`](Green54GaussianProjections.lean)

## Gaussian constants

Write γ for standard Gaussian measure in the dimension under discussion. Theorem 1.1 and Corollary 5.2 of Hua, Song and Tudose, with `b = c = 1/3`, give the finite input. For compact K with γ(K) > 5/6, the real dilation `3 · (K + K + K)` contains a compact convex C with γ(C) ≥ 1/3. Their body can also be chosen symmetric. The Lean hypothesis uses only convexity and compactness. [Hua–Song–Tudose, §5](https://arxiv.org/html/2605.10908v2#S5)

`finite_iff_countable` proves that this compact-input estimate in all finite dimensions is equivalent to the same estimate on ℝ^ℕ. Coordinate projections commute with sums and real dilations. For the converse, lift a finite input to its cylinder in ℝ^ℕ. Its mass exceeds 5/6, so inner regularity gives a compact subset still above the threshold. Project the resulting countable witness back onto the original coordinates.

Every point of `3 · (K + K + K)` is a sum of nine elements of K. This gives the countable nine-summand conclusion for arbitrary compact K. In DeepMind’s balanced case, positive mass makes K nonempty and balancedness gives 0 ∈ K. Adding zero gives a tenth summand. The final theorem `green_54_of_finite` has exactly the positive DeepMind conclusion under the finite hypothesis. An unconditional Lean proof of that finite hypothesis remains to be supplied. [Notebook replay](../README.md#replay)

## Three summands

Mazhar subsequently proved that if a finite-dimensional Gaussian set A has mass greater than 2/3, then A + A + A contains a compact convex set of mass at least 1/2 containing the origin. The notebook proves the countable compact-input mass conclusion from the finite theorem. More generally, `gaussian_sum_of_finite` preserves any fixed number of Minkowski summands and both mass thresholds. The specialization `gaussian_three_of_finite` uses the finite mass estimate as a hypothesis and gives mass at least 1/2 inside K + K + K, without a balance assumption. [Mazhar, Theorem 1.2, version 2](https://arxiv.org/html/2609.14832v2#S1)
