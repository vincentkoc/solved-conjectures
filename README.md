# Solved conjectures

A catalogue of [Vincent Koc](https://github.com/vincentkoc)'s formal Lean contributions to
[Left to Solve](https://lefttosolve.com) / [open-math-agents](https://github.com/GuillaumeBAUD-coder/open-math-agents),
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures), and related projects.

This is a personal contribution log, kept up to date as proofs, reductions, and notes land.
It is inspired by [1337isnot1337/solved-conjectures](https://github.com/1337isnot1337/solved-conjectures),
but it records work submitted to those host projects rather than a standalone research collection.

## AI assistance

Entries here were written with an AI coding agent (Grok Bot / Solver) and, for proofs and
reductions, kernel-checked before they were submitted. Dead-end notes are computational
evidence, not proofs. Each host pull request carries its own disclosure.

## Status

- **merged** — accepted into the host project (4)
- **open** — pull request still under review (1)
- **superseded** — closed because a later or competing solution landed (1)
- **closed** — closed without merge, for example a duplicate (1)
- **dead-end note** — public Left to Solve note on a failed or likely-false step (2)

Dates are calendar dates in Asia/Singapore for the status event (merge, close, open, or note).
The machine-readable source of truth is [`index.json`](index.json).
Lean files under [`proofs/`](proofs/) are exact copies of our submissions; they are not a Lake package.
See [`scripts/README.md`](scripts/README.md) for how later sessions should append entries.

## Contributions

| Project | Problem / step | Status | Link | Date (SGT) | Files |
| --- | --- | --- | --- | --- | --- |
| [open-math-agents](https://github.com/GuillaumeBAUD-coder/open-math-agents) | [`OeisA255916.conjecture_3.R1.H2`](https://lefttosolve.com/p/OeisA255916.conjecture_3.R1.H2) | dead-end note | [note 56352](https://lefttosolve.com/p/OeisA255916.conjecture_3.R1.H2) | 2026-11-28 | [`OeisA255916.conjecture_3.R1.H2.md`](notes/OeisA255916.conjecture_3.R1.H2.md) |
| [open-math-agents](https://github.com/GuillaumeBAUD-coder/open-math-agents) | [`OeisA255916.conjecture_2.R1.H2`](https://lefttosolve.com/p/OeisA255916.conjecture_2.R1.H2) | dead-end note | [note 56347](https://lefttosolve.com/p/OeisA255916.conjecture_2.R1.H2) | 2026-11-28 | [`OeisA255916.conjecture_2.R1.H2.md`](notes/OeisA255916.conjecture_2.R1.H2.md) |
| [open-math-agents](https://github.com/GuillaumeBAUD-coder/open-math-agents) | [`Green3.green_3.R2.H1.R1.H1`](https://lefttosolve.com/p/Green3.green_3.R2.H1.R1.H1) | superseded | [#7150](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7150), superseded by [#5869](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5869) | 2026-11-28 | [`Green3.green_3.R2.H1.R1.H1.lean`](proofs/open-math-agents/Green3.green_3.R2.H1.R1.H1.lean) |
| [open-math-agents](https://github.com/GuillaumeBAUD-coder/open-math-agents) | [`Erdos338.erdos_338.variants.triangular.R1.H1.R1.H1.R1.H1.R1.H2.R1.H1`](https://lefttosolve.com/p/Erdos338.erdos_338.variants.triangular.R1.H1.R1.H1.R1.H1.R1.H2.R1.H1) | open | [#7628](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7628) | 2026-11-27 | [`Erdos338.erdos_338.variants.triangular.R1.H1.R1.H1.R1.H1.R1.H2.R1.H1.lean`](proofs/open-math-agents/Erdos338.erdos_338.variants.triangular.R1.H1.R1.H1.R1.H1.R1.H2.R1.H1.lean) |
| [open-math-agents](https://github.com/GuillaumeBAUD-coder/open-math-agents) | [`oeis-a262779`](https://lefttosolve.com/p/oeis-a262779) | merged | [#5722](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5722) | 2026-11-27 | [`oeis-a262779.lean`](proofs/open-math-agents/oeis-a262779.lean) |
| [open-math-agents](https://github.com/GuillaumeBAUD-coder/open-math-agents) | [`oeis-a047946`](https://lefttosolve.com/p/oeis-a047946) | merged | [#5687](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5687) | 2026-11-27 | [`oeis-a047946.lean`](proofs/open-math-agents/oeis-a047946.lean) |
| [open-math-agents](https://github.com/GuillaumeBAUD-coder/open-math-agents) | [`Green3.green_3.R2.H1.R1`](https://lefttosolve.com/p/Green3.green_3.R2.H1) | merged | [#5570](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5570) | 2026-11-27 | [`Green3.green_3.R2.H1.R1.lean`](proofs/open-math-agents/Green3.green_3.R2.H1.R1.lean) |
| [open-math-agents](https://github.com/GuillaumeBAUD-coder/open-math-agents) | [`Green3.green_3.R2`](https://lefttosolve.com/p/Green3.green_3) | merged | [#5203](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5203) | 2026-11-27 | [`Green3.green_3.R2.lean`](proofs/open-math-agents/Green3.green_3.R2.lean) |
| [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) | [`Hanna exponential sequence initial-value tests`](https://github.com/google-deepmind/formal-conjectures/pull/8406) | closed (duplicate) | [#8406](https://github.com/google-deepmind/formal-conjectures/pull/8406) | 2026-11-27 | — |

## License

The catalogue, scripts, and notes are [MIT](LICENSE).
Archived Lean files remain contributions to their host projects; see the linked pull requests.
