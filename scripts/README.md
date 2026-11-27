# Updating this catalogue

After opening, merging, or closing a PR, or posting a dead-end note:

1. `git pull --ff-only origin main`

2. Verify the status immediately before writing it:

   ```bash
   gh pr view <number> --repo <owner/repo> --json number,title,state,mergedAt,closedAt,url
   ```

   Use `merged` only when `mergedAt` is set. A closed PR with `mergedAt: null`
   is `closed` or `superseded`. For a Left to Solve note, confirm the note id
   and step URL.

3. Upsert the entry and regenerate the README. Copy a Lean file only for
   merged or open proofs (and for a superseded proof that is still ours):

   ```bash
   scripts/add-entry \
     --id oma-1234 \
     --project open-math-agents \
     --project-url https://github.com/GuillaumeBAUD-coder/open-math-agents \
     --problem 'SomeProblem.step' \
     --label 'SomeProblem step' \
     --problem-url https://lefttosolve.com/p/SomeProblem.step \
     --kind proof \
     --status merged \
     --pr https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1234 \
     --pr-number 1234 \
     --date 2026-11-28 \
     --date-utc 2026-11-28T01:23:45Z \
     --lean path/to/submitted.lean \
     --notes 'Short description of what the PR or note does.' \
     --ai-assistance
   ```

   `--date` is a plain `YYYY-MM-DD` for the status event. `--date-utc` is the
   instant from `gh` (`mergedAt`, `closedAt`, or `createdAt` if still open).

   To update an existing entry, pass the same `--id` with the new `--status`
   and dates. The script upserts.

   For a dead-end note, use `--kind note`, `--status dead-end-note`,
   `--note-id <id>`, and `--notes-file` pointing at the posted text. Do not
   invent a PR number.

   `--id` is required. Convention: `oma-<pr>`, `formal-conjectures-<pr>`,
   `lts-note-<id>`.

4. `scripts/add-entry --check`

5. Commit the catalogue files and push `main`. Keep the commit scoped to the
   catalogue change.

Do not put names, emails, timezone, location, or local paths in catalogue
files. The public GitHub handle is enough. Dates are plain `YYYY-MM-DD`.

Statuses: `merged`, `open`, `superseded`, `closed`, `dead-end-note`.
Kinds: `proof`, `reduction`, `note`, `statement`.
