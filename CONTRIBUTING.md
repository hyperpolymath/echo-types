<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
# Contributing to echo-types

Echo is the standard dependent fibre, presented in Agda with scoped models of structured loss. Start with [README.adoc](README.adoc), the [roadmap](roadmap.adoc), and the [foundation and trust boundary](docs/foundation.adoc). The extracted ordinal programme belongs in `hyperpolymath/ordinal-notation`.

## Propose a change

Search existing issues, then describe the problem, expected behaviour, and a minimal reproduction or concrete proof obligation. For proof failures include the source revision, Agda version, dependency revisions, command, and complete diagnostic. For proposed theorems state the assumptions and distinguish source inspection from completed typechecking.

Use the fork-and-pull-request workflow with a focused `docs/`, `fix/`, or `feat/` branch from `main`. Keep unrelated work separate. Maintainers decide acceptance under [GOVERNANCE.adoc](GOVERNANCE.adoc); participation follows [CODE_OF_CONDUCT.adoc](CODE_OF_CONDUCT.adoc). Report vulnerabilities through [SECURITY.adoc](SECURITY.adoc).

## Check the change

Register the Agda standard library and absolute-zero library at the revisions recorded in [docs/foundation.adoc](docs/foundation.adoc). Then, from the repository root:

```sh
bash scripts/check-grade3.sh
```

This script runs the seven existing workflow roots with uncached interfaces and their declared profiles, plus static guards. For the additional bounded foundation-audit entrypoint and source manifest, see [the audit evidence](docs/audit/2026-11-06-evidence.adoc). Save stdout and stderr, including warnings; a successful root check covers its imports rather than every tracked file.

Ordinary proofs use `--safe --without-K --cubical-compatible`. The Cubical island is checked separately with `--safe --cubical`. The three existing guard exceptions are listed in the foundation document; they are not a general exemption for new files. Preserve termination, coverage, positivity, and the explicit trust boundaries. Do not introduce unsolved holes, postulates, unsafe primitives, or escape pragmas into the ordinary checked development. State any extra equality principle as an explicit hypothesis.

Keep theorem compatibility names stable where practical, and update affected imports, smoke pins, and documentation. Do not infer novelty from a scoped counterexample, single-use enforcement from duplicable values, or physical claims from arithmetic models. Retain dated retraction and proof records and append corrections. Record user-visible changes in [CHANGELOG.adoc](CHANGELOG.adoc).

## Commits and review

Use descriptive Conventional Commit messages and include the Developer Certificate of Origin sign-off (`git commit -s`). Follow the estate [signed-commit policy](https://github.com/hyperpolymath/standards/blob/ba640e9a57f22608710ffecdca282074eac55a0b/docs/SIGNING-POLICY.adoc). A DCO sign-off and a cryptographic signature serve different purposes.

Describe what changed, why, and the exact checks performed in the pull request. Kernel, bridge, aggregate, and guard changes need explicit maintainer review.

## Per-file licensing

The owner's November 6, 2026 policy for new original files is **CC-BY-SA-4.0 for prose documentation** and **MPL-2.0 for code, configuration and scripts**. Put the appropriate `SPDX-License-Identifier` and an accurate `SPDX-FileCopyrightText` in each file using its comment syntax. For formats that cannot contain comments, use a neighbouring `<filename>.license` sidecar. Choose the notice by the file's content, not merely its directory.

For edits to existing files, preserve their recorded notices and third-party attribution. The prospective default does not silently replace an existing file's licence; any scoped notice correction or relicensing needs its own recorded authority and affected paths. Historical grants and archived provenance remain documented in the [licence inventory and owner decision](docs/audit/2026-11-06-license-inventory.adoc).

This root guide is the current contribution entrypoint. `.github/CONTRIBUTING.md` points here; use the live foundation document for proof profiles and trust exceptions.
