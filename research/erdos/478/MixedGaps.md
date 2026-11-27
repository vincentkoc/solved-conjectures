# Erdős 478 — simultaneous factorial collisions

Write $A_p=\{k!\bmod p:1\le k<p\}$. For every $N$ there is a prime $p>N$ such that 5 is a square modulo $p$ and $|A_p|\le p-5$. This improves the notebook’s $p-4$ bound on an infinite subfamily. Erdős 478 asks for the limit of $|A_p|/p$ along all primes. A fixed deficit on a subsequence leaves that limit open. [Lean proof](Erdos478MixedGaps.lean) · [Previous bound](NOTES.md) · [Pinned upstream declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean)

## Counting distinct endpoints

For every prime $p>5$, let $Q_p$ and $C_p$ count the roots in $\mathbb F_p$ of $x(x-1)=1$ and $x(x-1)(x-2)=1$, respectively. `Erdos478.MixedGaps.card_add_root_counts` proves

$$|A_p|+Q_p+C_p+2\le p.$$

Each least nonnegative root representative $x$ repeats an earlier factorial at $x-2$ or $x-3$. A shared root would satisfy $x-2=1$ and $6=1$, forcing $p=5$. At $x=-2$ the two products are $6$ and $-24$, so Wilson’s repeat $(p-2)!\equiv1!$ has its own endpoint. Keeping the earliest index for each residue counts these endpoints even when their factorial values agree. For example, at $p=59$ the quadratic endpoints are $26,34$, the cubic endpoints are $5,14,43$, and Wilson supplies $57$. Removing those six indices from the original 58 gives $|A_{59}|\le52$.

The falling-factorial root method and stronger average results appear in Klurman–Munsch. The socialist-prime literature also uses the quadratic and cubic obstructions. The contribution here is a checked pointwise combination and an elementary certificate that both kinds of root occur for arbitrarily large primes. [Klurman–Munsch, §2](https://doi.org/10.5802/jtnb.974) · [Andrejić–Tatarević, §1](https://arxiv.org/abs/1603.04086)

## Forcing both roots above any cutoff

Set $M=\max(N,43)$, $u=10M!$, $a=u^3+3u^2+5u+1$ and $b=3u^2+3u+1$. Take any prime divisor of $a^2-ab-b^2$. This integer exceeds one: it equals $(a-2b)(a+b)+b^2$ with $a\ge2b$. Every prime at most $M$ divides $u$, at which the integer is $-1$ modulo that prime. Thus $p>M$.

In $\mathbb F_p$, if $b=0$ then $a=0$. But $3a-(u+2)b=8u+1$ and $64b-(24u+21)(8u+1)=43$, contradicting $p>43$. Therefore $x=a/b$ satisfies $x(x-1)=1$. Substitution gives a cubic endpoint $z=u+2-x$. The conjugate $1-x$ gives a second quadratic endpoint, distinct from $x$ because $(2x-1)^2=5\ne0$. The same identity proves that 5 is a square. These are the witnesses for `Erdos478.MixedGaps.arbitrarily_large_sub_five`.

## Scope and replay

The three public declarations use the exact factorial image in the upstream statement. The two pointwise declarations require a prime greater than five. The infinitude theorem takes only the cutoff. Live checks on 2026-11-28 found the DeepMind statement work, an unsolved and unclaimed LTS target, and no matching OMA proof or reduction. Related OMA hits concern sums of distinct factorials and a divisor-counting problem. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5229) · [LTS target](https://lefttosolve.com/p/Erdos478.erdos_478) · [OMA factorial-sum reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4056) · [OMA divisor count](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7450)

Run from the notebook root with `FC` set to the pinned Formal Conjectures checkout. The three axiom reports list only `propext`, `Classical.choice` and `Quot.sound`.

```bash
set -e
proof="$PWD/research/erdos/478/Erdos478MixedGaps.lean"
out="$(mktemp -d)"
cd "${FC:?set FC to the pinned checkout}"
lake env lean -DwarningAsError=true -R "$(dirname "$proof")" -o "$out/Erdos478MixedGaps.olean" "$proof"
lake env bash -c 'LEAN_PATH="$1:$LEAN_PATH" leanchecker -v Erdos478MixedGaps' _ "$out"
unlink "$out/Erdos478MixedGaps.olean"
rmdir "$out"
```
