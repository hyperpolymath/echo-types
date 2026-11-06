#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Validate declarations without executing their embedded probe strings.
set -euo pipefail

repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo"
standards=${ECHO_STANDARDS_DIR:-"$repo/../.echo-standards-references/standards"}
expected_revision=ba640e9a57f22608710ffecdca282074eac55a0b
bun=${BUN:-bun}
nickel=${K9_NICKEL:-nickel}

fail() { printf 'metadata: %s\n' "$*" >&2; exit 2; }
[[ -d "$standards/.git" ]] || fail "set ECHO_STANDARDS_DIR to the pinned standards checkout"
[[ $(git -C "$standards" rev-parse HEAD) == "$expected_revision" ]] || fail "standards revision must be $expected_revision"
for source in \
  1-formats/deed/tools/deed_lint.js \
  1-formats/k9/tools/k9-validate.sh \
  1-formats/k9/spec/contract/k9_contract.ncl; do
  # Compare the actual executable source bytes, without refreshing the entire
  # checkout index (which is costly on Windows-mounted workspaces).
  expected_blob=$(git -C "$standards" rev-parse "$expected_revision:$source")
  actual_blob=$(git -C "$standards" hash-object --no-filters "$source")
  [[ $actual_blob == "$expected_blob" ]] || fail "validator source differs from its pin: $source"
done
command -v "$bun" >/dev/null || fail "Bun is required (set BUN to its executable)"
command -v "$nickel" >/dev/null || fail "Nickel is required for semantic K9 validation (set K9_NICKEL)"

mapfile -d '' retired < <(find .machine_readable -type f -name '*.a2ml' -print0)
[[ ${#retired[@]} == 0 ]] || fail "retired .a2ml records remain: ${retired[*]}"
mapfile -d '' mirrors < <(find .machine_readable/svc -type f -print0 2>/dev/null || true)
[[ ${#mirrors[@]} == 0 ]] || fail "retired duplicate svc metadata remains: ${mirrors[*]}"
mapfile -d '' deeds < <(find . -maxdepth 1 -type f -name '*_chora.deed' -print0)
[[ ${#deeds[@]} == 1 && ${deeds[0]} == ./echo-types_chora.deed ]] || fail "exactly one root echo-types_chora.deed is required"
[[ ! -e 0-AI-MANIFEST.deed ]] || fail "descriptive metadata belongs in the single chora deed"

tmp=$(mktemp -d)
trap 'rm -rf -- "$tmp"' EXIT
"$bun" "$standards/1-formats/deed/tools/deed_lint.js" --ast-json echo-types_chora.deed > "$tmp/chora.json"
"$bun" -e '
  const ast = JSON.parse(require("node:fs").readFileSync(process.argv[1], "utf8"));
  const fail = message => { throw new Error(message); };
  const field = (items, name, kind, expected) => {
    const found = items.filter(x => x[0] === "field" && x[1] === name);
    if (found.length !== 1 || found[0][2][0] !== kind || found[0][2][1] !== expected)
      fail(`identity mismatch or duplicate: ${name}`);
  };
  const clause = name => {
    const found = ast.items.filter(x => x[0] === "clause" && x[1] === name);
    if (found.length !== 1) fail(`required unique clause: ${name}`);
    return found[0][2];
  };
  if (ast.head !== "repo-deed") fail("expected repo-deed");
  field(ast.items, "canonical-name", "string", "echo-types");
  // This pinned canonical AST intentionally elides UUID bodies as null.
  // First establish their unique structural positions and types with it.
  field(ast.items, "repo-uuid", "uuid8", null);
  field(ast.items, "beholding-chora", "uuid5", null);
  // Read only the two typed literal spans after the canonical grammar gate.
  // Whole comments and strings are consumed first, preventing spoofed UUIDs
  // in prose from satisfying the identity check. JSON handles the four
  // escapes permitted in canonical DEED strings; no grammar is forked here.
  const source = require("node:fs").readFileSync("echo-types_chora.deed", "utf8");
  const literalTokens = /;[^\r\n]*|"(?:[^"\\]|\\["\\nt])*"|#u[58]"(?:[^"\\]|\\["\\nt])*"/g;
  const uuids = [...source.matchAll(literalTokens)].map(x => x[0]).filter(x => x.startsWith("#u"));
  if (uuids.length !== 2) fail("exactly the two structural identity UUID literals are expected");
  const bodies = new Map(uuids.map(x => [x.slice(0, 3), JSON.parse(x.slice(3))]));
  if (bodies.get("#u8") !== "gv-clade-index:github.com/hyperpolymath/echo-types"
      || bodies.get("#u5") !== "estate/chora") fail("recorded UUID preimage mismatch");
  field(clause("identity"), "owner", "string", "hyperpolymath");
  field(clause("identity"), "prefixed-name", "string", "fv-echo-types");
  field(clause("clade"), "primary", "symbol", "fv");
  field(clause("clade"), "primary-name", "string", "Formal Verification & Proofs");
  field(clause("forges"), "github", "string", "hyperpolymath/echo-types");
  console.log("DEED grammar and recorded registry identity: PASS");
' "$tmp/chora.json"

components=(coordination.k9.ncl .machine_readable/self-validating/examples/project-metadata.k9.ncl)
for verb in must trust adjust dust bust intend; do
  components+=(".machine_readable/contractiles/$verb/$verb.k9.ncl")
  [[ -f ".machine_readable/contractiles/$verb/$verb.ncl" ]] || fail "missing $verb paired schema"
  "$nickel" typecheck ".machine_readable/contractiles/$verb/$verb.ncl"
done
actual=()
while IFS= read -r -d '' component; do
  [[ -f $component ]] && actual+=("$component")
done < <(git ls-files -z --cached --others --exclude-standard -- '*.k9.ncl')
[[ ${#actual[@]} == 8 ]] || fail "expected eight active K9 components across the repository, found ${#actual[@]}: ${actual[*]}"
bash "$standards/1-formats/k9/tools/k9-validate.sh" --strict --no-route --nickel "$nickel" "${components[@]}"
printf 'Metadata grammar and K9 semantic checks passed; declared probes were not executed.\n'
