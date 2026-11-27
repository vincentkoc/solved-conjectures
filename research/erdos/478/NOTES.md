# Erdős 478 — factorial collisions

**Partial coverage.** For every prime $p>5$ for which 5 is a square modulo $p$, `Erdos478.card_factorial_residues_le_sub_four` proves $|A_p|\le p-4$ for the upstream set $A_p=\{k!\bmod p:1\le k<p\}$. The pinned declaration `Erdos478.erdos_478` asks whether $|A_p|/p\to 1-1/e$ along all primes. A fixed deficit on this class of primes leaves that limit open. [DeepMind source at f606af160664c5a10952e9a957b100a1cd45bbeb](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean) · [Problem 478](https://www.erdosproblems.com/478)

**Argument.** The two distinct roots of $x(x-1)\equiv 1\pmod p$ each give $x! \equiv (x-2)!\pmod p$ for their least representatives $x\ge3$. Neither root is $p-2$, since that would force $p\mid5$. Wilson gives a third repeated index, $(p-2)! \equiv 1!\pmod p$. Keeping the least index for each residue discards all three even if some of their values coincide. The quadratic obstruction is classical. [Trudgian, §1, pp. 1–2](https://arxiv.org/pdf/1310.6403)

**Duplicate check, 2026-11-28.** Open and closed DeepMind and OMA records were searched by number, declaration, file path, subject, and A210184. DeepMind recorded statement work. No matching proof or in-flight proof appeared. LTS listed both 478 and A210184 as unsolved and unclaimed. A210184 asks for a lower bound. The OMA proof and reduction trees had no matching entry. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [Closed statement PR](https://github.com/google-deepmind/formal-conjectures/pull/4078) · [Merged statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5229) · [LTS 478](https://lefttosolve.com/p/Erdos478.erdos_478) · [LTS A210184](https://lefttosolve.com/p/oeis-a210184) · [OMA search](https://github.com/GuillaumeBAUD-coder/open-math-agents/pulls?q=is%3Apr+Erdos478)

**Replay** from the research worktree. The final axiom report lists only `propext`, `Classical.choice`, and `Quot.sound`.

```sh
proof="$PWD/research/erdos/478/Erdos478FactorialCollisions.lean"
source ~/formal-math/env.sh
(cd ~/formal-math/fc && lake env lean "$proof")
```
