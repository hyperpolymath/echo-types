#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Ddraig accepts Markdown; canonical documentation remains AsciiDoc.
set -euo pipefail

repository="${GITHUB_REPOSITORY:?GITHUB_REPOSITORY is required}"
revision="${GITHUB_SHA:?GITHUB_SHA is required}"
if [[ ! "$repository" =~ ^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$ ]] ||
   [[ ! "$revision" =~ ^[0-9a-fA-F]{40}$ ]]; then
  printf 'Expected a GitHub owner/repository and a full commit SHA.\n' >&2
  exit 2
fi
root="$(cd "$(dirname "$0")/.." && pwd)"
destination="${1:-src}"
documents=(README.adoc docs/echo-types/what-echo-is.adoc PROOF-STATUS.adoc
  docs/build.adoc tutorial/README.adoc docs/theorem-index.adoc docs/echo-types/MAP.adoc)
for document in "${documents[@]}"; do
  test -f "$root/$document" || {
    printf 'Missing canonical documentation: %s\n' "$document" >&2
    exit 1
  }
done
base="https://github.com/$repository/blob/$revision"
mkdir -p "$destination"
cat > "$destination/index.md" <<EOF
---
title: Echo Types
description: Constructive Agda proofs about fibres, composition, and structured loss.
---
# Echo Types

Constructive Agda proofs about fibres, composition, and structured loss.
Read the definitions, assumptions, and limitations in the canonical documentation.

- [Project overview]($base/README.adoc)
- [What Echo is and the scope of its claims]($base/docs/echo-types/what-echo-is.adoc)
- [Proof status and assumptions]($base/PROOF-STATUS.adoc)
- [Build and verification instructions]($base/docs/build.adoc)
- [Tutorials]($base/tutorial/README.adoc)
- [Theorem index]($base/docs/theorem-index.adoc)
- [Module and claim map]($base/docs/echo-types/MAP.adoc)

These links open the repository's AsciiDoc documents at the source revision
used for this site. This landing page does not render or certify those documents.
EOF
