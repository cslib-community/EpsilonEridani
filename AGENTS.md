# Working in Epsilon Eridani

This is the AI-authored code repository of Epsilon Eridani. `README.md` says what the project
is, how to build, and how to run a worker; this file adds only the contract for agents.

## Before you write code

**Read the roadmap first.** Roadmaps live in
[EpsilonEridaniRoadmap](https://github.com/cslib-community/EpsilonEridaniRoadmap), one
directory per area; the area's `README.md` is the specification and `Suggested.lean` is
optional guidance. The roadmap gates *new* computer science: add a new declaration or file only
when it advances a specific roadmap target or supplies a prerequisite that target needs. If what
you want to build is not on the roadmap, pick a supported target instead. Never open a PR or
an issue in EpsilonEridaniRoadmap yourself.

Improving existing code is **always in scope** and needs no roadmap entry: refactoring,
simplifying proofs, modest generalisation, relocation, cleaner idioms, and documentation.

There is no claims system. Open PRs are the only signal that a target is being worked on, so
check them before starting one.

Every PR description carries one standalone line, `Roadmap: CanonicalAreaName` or
`Roadmap: none`, using the roadmap directory name. New computer science must also cite the
roadmap file and target it advances; a refactor names the roadmap chiefly motivating it;
general, infrastructure, or dependency work uses `none`. Directory names under
`EpsilonEridani/` do not determine the roadmap area.

## Dependencies, reuse, and layout

CSLib is the direct dependency; Mathlib, Batteries, and Lean core come through it. Before
introducing an interface, search in that order: CSLib, Mathlib, Batteries, then Lean core and
Std. Reuse what you find; the surrounding code and the roadmap break ties. Both CSLib and
Mathlib are upstream destinations, so write general material so it could move to CSLib
without redesign.

Code goes only under `EpsilonEridani/`, in a tree that mirrors CSLib's so a module could move
upstream without changing its path. A roadmap's proposed layout is the default.

## The rules of the repo

- `main` is always green. CI enforces no `sorry`, the standard axioms only (so no
  `native_decide`), the module system in every file, and the Mathlib linter set. Do not try
  to disable any of it.
- Library code is computer science, not metaprogramming. `set_option`, heartbeat
  instrumentation, meta and unsafe declarations, elaborators, initializers, and `#eval` are
  rejected by `scripts/check_source_options.py`. Local macros are allowed when they remove
  substantial repeated proof machinery; prefer named definitions and lemmas to custom syntax.
- Executable definitions stay computable and keep what they compute through refactors.
- One topic per PR. A prerequisite refactor is its own PR.
- No stacked PRs, drafts included. Wait for a prerequisite to land, then rebase and open the
  dependent PR with only the new work.
- No backwards compatibility. When a declaration moves, is renamed, or is superseded by CSLib
  or Mathlib, update every in-repository use and delete the old name in the same PR. No
  aliases, wrappers, forwarding modules, or deprecated shims.
- Everything outside `EpsilonEridani/` is human-owned: `scripts/`, `.github/`,
  `tauceti.toml`, the lakefile, `docs/`, `README.md`, and this file. Agents may propose a
  **forward-only** bump of `lake-manifest.json` and `lean-toolchain`; `bump-guard` validates
  it and a human merges it. CSLib's `rev` stays `main`, Mathlib's revision follows CSLib's
  pin, and no PR edits the lakefile or moves a pin backward.
- Copyright headers name the human contributor whose account authored the PR.
- **Never strip a PR's human-owned changes to get it past the gate.** They are the deliverable;
  the gate routes such a PR to a human on purpose. Fix and review agents skip those PRs.
- **Do not `--admin`-merge AI-authored PRs.** Landing a PR is the review pipeline's job. If no
  verdicts are appearing, run the review or leave the PR for a human.

## How review works

Open a PR. After CI passes, AI reviewers judge it against the
[TauCetiReview](https://github.com/TauCetiProject/TauCetiReview) rubrics and post
`approve` / `request_changes` / `block` verdicts. Nothing in this repository schedules those
reviews: a contributor or worker runs `tauceti-review` against this project's `tauceti.toml`
(see the README) and `--post` publishes a scoreboard pinned to the reviewed commit. A new push
invalidates it, so after addressing findings the PR waits for another review run.

If two findings contradict, contest one thread, link the other, quote both wordings, and
explain why both cannot hold.

When the scoreboard for the current commit is all green, CI is green, and the PR changes only
`EpsilonEridani/`, the merge queue **merges it automatically**. Every other PR waits for human
review and an admin merge; see [`docs/automation.md`](docs/automation.md).
