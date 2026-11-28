# Green 33 · graph rows at orders 130 and 238

The 18-label seed modulo 130 uses a character graph at even parity and a vertical fiber at odd parity. Replacing the two fields of orders 13 and 5 by fields of orders 17 and 7 would give 24 labels modulo 238 and improve the normalized size from 18/√130 ≈ 1.578704 to 24/√238 ≈ 1.555689. **Every function in the order-238 construction fails.** The theorem `no_cyclic_axis_238` gives the exclusion in the cyclic group itself. It leaves unrestricted 24-label seeds at order 238 open. [Lean proof](Green33GraphRows.lean) · [Order-130 seed and Lewis attribution](QUARTIC-SEED.md) · [Lift to all large multiples](ALL-SEED-MULTIPLES.md)

## The row obstruction

Let H and K be finite abelian groups of orders p and q. At parity zero take the graph of an arbitrary function f from H to K. At parity one take the entire K fiber over zero in H. To cover a target (0,r,z) with r nonzero, two distinct graph points must contribute. Thus each nonzero row r has to contain every color z as f(a)+f(r−a) with a ≠ r−a. At order 238 the CRT identifies these coordinates with the original cyclic group. [Row predicate, cardinality and CRT](Green33GraphRows.lean)

Write R(r,z) for the number of ordered witnesses, including equal inputs, and D(r,z) for the number of a with f(a)−f(a−r)=z. If p=2q+h, the exceptional row obeys

```text
Σ_z R(0,z)² ≥ p² − (p−1)h(h−1).
```

Indeed, each nonzero sum row starts with two witnesses at each color and distributes h further witnesses. Its squared counts sum to at most 4q+4h+h². Each difference row has the same mass, and each integer entry d satisfies d²+6 ≥ 5d. This gives a lower bound of 4q+5h for its squared counts. Total sum and difference energies agree. The zero difference row puts all p witnesses at zero, giving the displayed inequality. If h=3 and p≥14, at least p−3 inputs a satisfy **f(a)+f(−a)=z** for one fixed z. [Energy identity](Green33TailEnergy.lean) · [Graph reflection bound](Green33GraphRows.lean)

At p=2q+1, with q≥3 and injective doubling in both groups, complete nonzero rows are impossible. In row 2i with i nonzero, the one excess ordered witness must occur at 2f(i), since the diagonal adds a third witness to the strict pair for that color. Summing colors over the row makes 2f(i) independent of i. Injectivity forces a constant on the nonzero inputs, leaving at most two colors in a nonzero row. [Saturation theorem](Green33GraphRows.lean)

## The seven color frequencies

For p=17 and q=7 the eight distinct-input unordered pairs in row 2i, i ≠ 0, must realize all seven colors. Exactly one color occurs twice. The eight pairs partition the domain outside i. Their color sum is S−f(i), where S is the sum of f over its domain. The sum of all seven colors is zero, so S−f(i) is the repeated color. Restoring the orders and the diagonal gives two witnesses at every color, two more at S−f(i), and one more at 2f(i).

Translate the output by −5S so its total becomes zero in the field of order seven. Let c(z) count how often the translated function takes value z, and let v denote its value at zero. Define

```text
P(z) = Σ_t c(t)c(z−t)       B(z) = 32 + 2c(−z) + c(4z).
```

Summing the nonzero-row formula proves the exact identity **P(z)+2[−v=z]+[2v=z] = B(z)+R(0,z)**. The bracket is one when the equality holds and zero otherwise. Nonnegativity forces the sum of the positive parts of B−P to be at most 3. Reflection forces B(z)+14 ≤ P(z)+3 for at least one z.

There are exactly 100,947 nonnegative seven-part compositions of 17. The separate Lean certificate checks that every one violates at least one of those necessary conditions. It uses integer arithmetic and kernel reduction. The exclusion is independent of the choice of f, its symmetry and any multiplicative-character assumption. [Seven-frequency certificate](Green33GraphHistogram.lean) · [Exact histogram identity](Green33GraphRows.lean)

## Scope and verification

The pinned Green 33 asks for ordinary sumset equality on infinitely many positive moduli with normalized size tending to √2. This obstruction concerns one construction of strict covers. The unrestricted ordinary problem at 238 and the pinned endpoint remain open here. Haanpää enumerated strict bases in small abelian groups through order 90. Fu, Feng, Wang and Carlet study derivative imbalance in maps between finite abelian groups. Their difference spectra provide related energy terminology. [Pinned statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Haanpää](https://cs.uwaterloo.ca/journals/JIS/VOL7/Haanpaa/haanpaa.pdf) · [Fu–Feng–Wang–Carlet](https://arxiv.org/abs/1710.07765)

Both new modules and the four notebook dependencies were compiled from source with Lean 4.33.1 and independently replayed with `leanchecker`. All twelve public theorems report only `propext`, `Classical.choice`, and `Quot.sound`. Codex assisted with the formalization. [Replay](../README.md#replay) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33) · [Open Math Agents](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues?q=%22reflection%22+%22sum+cover%22)
