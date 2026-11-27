# Updating this catalogue

Do this on vcuriosity, in `~/GIT/_Perso/solved-conjectures`, after opening or
merging a PR, closing one, or posting a dead-end note. Never run `git` or `gh`
from the shared agent box.

## Procedure

1. Pull the latest main, without rewriting history:

   ```bash
   cd ~/GIT/_Perso/solved-conjectures
   git pull --ff-only origin main
   ```

2. Verify the status immediately before writing it.

   For a pull request:

   ```bash
   gh pr view <number> --repo <owner/repo> --json number,title,state,mergedAt,closedAt,url
   ```

   Use `MERGED` only when `mergedAt` is set. A closed PR with `mergedAt: null`
   is `closed` or `superseded`, not merged. For a Left to Solve note, confirm
   the note id and step URL on the step page.

3. Upsert the entry and regenerate `README.md` from `index.json`. Copy a Lean
   file only for merged or open proofs (and for a superseded proof that is
   still ours and worth keeping):

   ```bash
   scripts/add-entry \
     --id oma-1234 \
     --project open-math-agents \
     --project-url https://github.com/GuillaumeBAUD-coder/open-math-agents \
     --problem 'SomeProblem.step' \
     --problem-url https://lefttosolve.com/p/SomeProblem.step \
     --kind proof \
     --status merged \
     --pr https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1234 \
     --pr-number 1234 \
     --date 2026-11-28 \
     --date-utc 2026-11-28T01:23:45Z \
     --lean /path/to/submitted.lean \
     --notes 'Short description of what the PR or note does.' \
     --ai-assistance
   ```

   `--date` is the calendar date of the status event in Asia/Singapore.
   `--date-utc` is the same instant in UTC, taken from `gh` (`mergedAt`,
   `closedAt`, or `createdAt` for an still-open PR).

   To update an existing entry (for example an `open` PR that has since
   merged), pass the same `--id` and the new `--status` / dates. The script
   upserts.

   For a dead-end note, use `--kind note`, `--status dead-end-note`,
   `--note-id <id>`, and `--notes-file` pointing at the posted text (it is
   copied into `notes/`). Do not invent a PR number.

   `--id` is required. Convention: `oma-<pr>` for open-math-agents,
   `formal-conjectures-<pr>` for formal-conjectures, `lts-note-<id>` for a
   Left to Solve note.

4. Confirm the index and README agree, and that listed files exist:

   ```bash
   scripts/add-entry --check
   ```

5. Commit with the per-repo noreply address and signed commits, then push
   `main`. Never disable `gpgsign` globally.

   ```bash
   git config --local user.email 25068+vincentkoc@users.noreply.github.com
   git config --local user.name "Vincent Koc"
   git add index.json README.md proofs notes
   git status
   git commit -m "Add OMA #1234 SomeProblem.step (merged)"
   git push origin main
   ```

   Keep the commit scoped to the catalogue change. Do not commit unrelated
   dirty files.

Statuses: `merged`, `open`, `superseded`, `closed`, `dead-end-note`.
Kinds: `proof`, `reduction`, `note`, `statement`.
