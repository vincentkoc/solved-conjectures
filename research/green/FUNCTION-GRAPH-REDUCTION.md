# Green 50 reduced to graphs of functions

Every nonempty set A of density α in the binary cube has a full function graph inside A+A. Its output space has dimension at most `log₂(1/α)`. Consequently, Green 50 would follow from the following assertion for a fixed positive C. In every decomposition of the n-cube as U ⊕ V, five sums of the graph of any function from U to V contain an affine subspace of dimension at least `n − C dim(V)`. The five-summand graph assertion and the unrestricted ten-summand conjecture remain open. [Lean proof](Green50Graphs.lean) · [DeepMind statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/50.lean)

## Construction

Take a subspace V of maximal dimension with `V ∩ (A+A) = {0}`. The map sending (a,v) to a+v is injective on A × V, so `|A||V| ≤ 2ⁿ`. Every coset of V meets A+A. If x+V missed A+A, adjoining x to V would give a larger subspace with the same intersection property, since the larger subspace is precisely the union of V and x+V.

Choose a linear complement U. For each u in U pick a point of A+A in u+V, and write it as u+f(u). These points form the required graph. This is the quotient-kernel argument familiar from finite-field modeling. The minimal-quotient surjectivity step is the case t = 1 of Question 3 in UC San Diego’s 2024 additive combinatorics exercises. [UC San Diego, Homework 2](https://cseweb.ucsd.edu/classes/fa24/cse291-e/hw2.pdf#page=1) · [Zhao, §7.7, Proposition 7.7.1](https://ocw.mit.edu/courses/18-225-graph-theory-and-additive-combinatorics-fall-2023/mit18_225_f23_lec22-25.pdf)

## What transfers

For any k and any nonnegative C, a k-summand bound for all full graphs gives a 2k-summand bound for all sets, with the same C. Conversely, a k-summand bound for all sets gives the k-summand graph bound directly, since the reciprocal density of a graph is exactly the size of its output space. Thus existence of *some* fixed summand count with logarithmic codimension is equivalent in the two formulations. At the specified count of ten, the proved implication uses five graph summands. [Notebook replay](../README.md#replay)
