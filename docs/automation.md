# Automation App and secrets

How EpsilonEridani's GitHub automation authenticates, where its credentials live, and what to
do when they need to change. For the general Tau Ceti setup, see the
[project setup guide](https://github.com/TauCetiProject/TauCetiTools/blob/main/docs/project-setup.md#apps-and-credentials).

## The App

- **Name:** `EpsilonEridani-automation`, owned by the `cslib-community` organization
  (App ID `5429897`; not secret).
- **Installed on:** `cslib-community/EpsilonEridani` only.
- **Repository permissions:** Actions, Checks, Commit statuses, Contents, Issues, Pull requests
  and Workflows: read and write; Variables: read-only. No organization or account permissions.
  Webhook inactive.
- **Managed by:** organization owners and GitHub App managers.

## Where the credentials are

| Location | Contents | Access |
|---|---|---|
| Repository Actions secrets `APP_ID`, `APP_PRIVATE_KEY` | App ID and the App's private key (PEM) | Write-only through the UI and API; exposed to workflow runs in this repository and masked in logs |
| The App's settings page | Fingerprints of active keys only; GitHub does not keep private keys | App managers and organization owners |
| Maintainer's machine (optional) | `~/.config/tauceti/projects/cslib-community__epsiloneridani/automation/{APP_ID,APP_PRIVATE_KEY}`, directory mode 0700, files 0600 | That maintainer only |

Never commit a key, paste it into an issue, PR or chat, or pass it as a command-line argument.
Upload it with stdin:

```sh
gh secret set APP_PRIVATE_KEY --repo cslib-community/EpsilonEridani < path/to/APP_PRIVATE_KEY
```

The repository also has the non-secret Actions variable `MERGE_BACKEND=queue`: automation
merges through GitHub's merge queue.

## How workflows use them

Trusted workflows call `actions/create-github-app-token` with the two secrets. That step mints
an installation token that expires after about an hour, is limited to this repository, and is
narrowed further to the permissions each job requests. Later steps use only that token.
Contributor PR code is built in the sandboxed `pr-build` harness, which runs the default
branch's workflow definition and does not expose these secrets to the candidate.

## Who can reach the secrets

Anyone with **write or admin** access to this repository can run a workflow with secrets:
the `main` ruleset requires code-owner review for workflow changes there, but a pushed branch
with a modified workflow also receives them. Keep write access limited to trusted maintainers,
and review collaborator and team access when people join or leave.

## Merging human-owned changes

The `main` ruleset ("Tau Ceti content") requires a pull request, code-owner review, the
`build`, `bump-guard` and `scope` checks and the merge queue, and blocks deletion and force
pushes. Changes outside `EpsilonEridani/` (configuration, workflows, lakefiles, docs) keep
`scope` red by design, and a changed lakefile is never executed by the trusted build. After
review, a repository administrator lands such a PR with GitHub's admin merge:

```sh
gh pr merge PR_NUMBER --repo cslib-community/EpsilonEridani --admin --squash
```

The only bypass actor is the repository admin role, for pull requests only; the automation App
is deliberately not on the bypass list, so automated merges always pass the required checks.

## Rotating the key

1. On the App's settings page, under **Private keys**, click **Generate a private key**.
2. Upload the new PEM with `gh secret set APP_PRIVATE_KEY ...` as above, and replace any local
   copy.
3. Confirm a workflow run succeeds, for example `PR status`, with its
   `create-github-app-token` step passing.
4. Delete the old key on the App's settings page.

## If a key may have leaked

1. Delete that key on the App's settings page. This revokes it immediately.
2. If the App itself may have been misused, suspend or uninstall it from the organization's
   installed GitHub Apps.
3. Generate and upload a new key as in [Rotating the key](#rotating-the-key).
4. Review recent activity by the App's bot account in this repository's pull requests, commits,
   issues and Actions runs.
