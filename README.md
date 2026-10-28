# Epsilon Eridani

Epsilon Eridani is a Lean library for computer science, built by AI contributors under
human direction. Humans decide what is worth formalizing; agents write the code and
subject it to public, adversarial review.

Our aim is to build a useful, coherent body of formalized computer science that others
can build on. That means reusable definitions, interfaces that fit the surrounding
library, and enough supporting theory to make the next development easier. A proof of
the headline theorem is a beginning; the library around it matters too.

We build on [CSLib](https://github.com/leanprover/cslib) and use the contribution and
review machinery developed for [Tau Ceti](https://github.com/TauCetiProject/TauCeti).
This is an experiment in growing an open library through human judgment and AI labor.
There is plenty to figure out, and we'd welcome your help!

## The repositories

- **EpsilonEridani** (this repository) holds the Lean implementations.
- **[EpsilonEridaniRoadmap](https://github.com/cslib-community/EpsilonEridaniRoadmap)**
  holds the human-approved specifications that direct the work.
- **[TauCetiReview](https://github.com/TauCetiProject/TauCetiReview)** supplies the
  shared review engine and rubrics. The versions used here are pinned in
  [`tauceti.toml`](tauceti.toml).

Humans can help by proposing roadmaps, reviewing their mathematical content, and
raising issues about definitions or implementations. AI contributors implement those
plans and tend their pull requests through review. Humans also maintain the project
configuration, infrastructure, and review policy.

The project is getting started. The Lean packages and core automation are in place;
the roadmap has no approved subject areas yet. Writing and reviewing the first
roadmaps is an especially useful way to contribute.

## Working with CSLib and Mathlib

CSLib is our direct dependency. Mathlib comes through CSLib, whose dependency pin
selects the Mathlib revision. The committed `lean-toolchain` and `lake-manifest.json`
record the versions used to build this library.

Reuse the definitions and conventions in those libraries wherever they fit. Search
existing declarations and ongoing upstream work before introducing another interface
for the same concept. As dependencies evolve, we want to adopt their APIs and keep
Epsilon Eridani compatible with them.

The dependency updater proposes advances of CSLib's `main` branch. Those changes
still need working builds and review; workers can help repair source code when an
upstream change requires it.

## Review

Lean checks proofs against their statements. Review also has to ask whether those
statements express the intended computer science, whether the definitions are useful,
and whether the code belongs in the library.

Implementation PRs first pass CI, including build, axiom, lint, and scope checks.
Agents then review the passing code using the shared
[rubrics](https://github.com/TauCetiProject/TauCetiReview/tree/main/rubrics), covering
correctness, reuse, scope, attribution, API design, generality, placement, naming,
documentation, and proof quality. Authors can revise their code or contest a finding
with an explanation. Review verdicts identify the commit they assessed.

Reviews can be run from the command line using a contributor's own agent subscription.
With [uv](https://docs.astral.sh/uv/) and the
[review prerequisites](https://github.com/TauCetiProject/TauCetiReview/blob/main/REVIEWING.md):

```bash
export TAUCETI_CONF=https://raw.githubusercontent.com/cslib-community/EpsilonEridani/main/tauceti.toml

# Review PR #42 without posting anything.
uvx --from git+https://github.com/TauCetiProject/TauCetiReview@fc9a57c67bf375ff349abc15c91f7fdb3ad2d486 \
  tauceti-review 42 --conf "$TAUCETI_CONF" --no-coordinate

# Replace --no-coordinate with --post to coordinate and publish the review.
```

Eligible implementation PRs go through GitHub's merge queue after the required checks
and review pass. Human-owned changes to configuration and infrastructure need human
review; see [automation and merge administration](docs/automation.md).

## Building

Install [Lean through elan](https://lean-lang.org/install/) and clone this repository,
then run:

```bash
lake exe cache get
lake build
```

Lake uses the committed toolchain and dependency pins. The cache command downloads
Mathlib's compiled dependencies; it does not provide an Epsilon Eridani build cache.
The root module intentionally has no imports, and Lake builds the source modules
through the library's configured globs. Import individual `EpsilonEridani.*` modules
when using the library.

## Contributing with a worker

The [Tau Ceti worker](https://github.com/TauCetiProject/TauCetiWorker) can work on this
project using its canonical configuration. It needs `git`, an up-to-date `gh`, `uv`,
`jq`, a Lean toolchain, and an authenticated agent CLI such as Codex or Claude. The
worker uses your GitHub identity and authors through your fork.

By default, workers run agents directly on your host with sandboxing and permission
prompts bypassed. To run eligible code and review tasks in a container, set up
[Bubble](https://github.com/TauCetiProject/TauCetiWorker/blob/main/docs/sandbox.md)
and add `--bubble` to the `work` commands below. The sandbox guide covers its runtime
and proxy requirements. Progress-report tasks still run on the host.

```bash
uv tool install git+https://github.com/TauCetiProject/TauCetiWorker
gh auth login
# Also authenticate the agent CLI you intend to use.
export TAUCETI_CONF=https://raw.githubusercontent.com/cslib-community/EpsilonEridani/main/tauceti.toml

tauceti --conf "$TAUCETI_CONF" doctor
tauceti --conf "$TAUCETI_CONF" status
tauceti --conf "$TAUCETI_CONF" work --dry-run
tauceti --conf "$TAUCETI_CONF" work
```

Read the relevant roadmap before implementing a target. Start with one round so you
can see the complete process before running `work --loop`. The usual worker cascade
prioritizes maintenance and review before opening new roadmap PRs. A review-only
worker uses `work --only review`; the upstream worker guide covers persistent workers
and subscription pacing.

Always select this project's configuration when invoking the shared tools. Their
unconfigured defaults can refer to Tau Ceti.

## Project setup

[`tauceti.toml`](tauceti.toml) records the enabled features and service choices.
Shared claims, review and CI archives, published API documentation, and generated
progress reports are currently disabled. Creating their repositories alone does not
enable those integrations. Coordinate substantial work through roadmap issues and PRs
while the project is establishing its contribution process.

Maintainers can consult the [Tau Ceti setup guide](https://github.com/TauCetiProject/TauCetiTools/blob/main/docs/project-setup.md)
and this repository's [automation guide](docs/automation.md). Doctor checks setup;
useful roadmaps, available workers, and a healthy review queue also need ongoing care.

The library is released under the [Apache 2.0 license](LICENSE).
