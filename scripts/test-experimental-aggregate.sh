#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Regression controls for aggregate wiring; no Agda source is modified.
set -euo pipefail
checker="$(cd "$(dirname "$0")" && pwd)/check-experimental-aggregate.sh"
fixture="$(mktemp -d)"
trap 'rm -rf "$fixture"' EXIT
printf 'module experimental.echo-additive.Grade where\n' > "$fixture/Grade.agda"

printf 'open import experimental.echo-additive.Grade\n' > "$fixture/All.agda"
bash "$checker" "$fixture" >/dev/null

printf '{-\nopen import experimental.echo-additive.Grade\n-}\n' > "$fixture/All.agda"
if bash "$checker" "$fixture" > "$fixture/block.log" 2>&1; then
  echo 'ERROR: block-commented import was accepted' >&2
  exit 1
fi
grep -q 'Missing aggregate import: Grade' "$fixture/block.log"

printf '{-\n{- nested -}\nopen import experimental.echo-additive.Grade\n-}\n' > "$fixture/All.agda"
if bash "$checker" "$fixture" > "$fixture/nested.log" 2>&1; then
  echo 'ERROR: nested-block-commented import was accepted' >&2
  exit 1
fi
grep -q 'Missing aggregate import: Grade' "$fixture/nested.log"

printf '%s\n' '-- open import experimental.echo-additive.Grade' > "$fixture/All.agda"
if bash "$checker" "$fixture" > "$fixture/line.log" 2>&1; then
  echo 'ERROR: line-commented import was accepted' >&2
  exit 1
fi

printf '%s\n' 'label = "{- not a block comment -}"' \
  'open {- inline comment -} import experimental.echo-additive.Grade' > "$fixture/All.agda"
bash "$checker" "$fixture" >/dev/null
echo 'Experimental aggregate controls: PASS (active imports accepted; commented imports rejected)'
