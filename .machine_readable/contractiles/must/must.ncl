# SPDX-License-Identifier: MPL-2.0
# Canonical must schema/run-policy data adapted for echo-types.
# This expression does not execute probes; root recipes execute checks.
let base = import "../_base.ncl" in

{
  pedigree =
    base.pedigree_schema
    & {
      contractile_verb = "must",
      semantics = "invariant",
      security = {
        leash = 'Kennel,
        trust_level = "read-only verification",
        allow_network = false,
        allow_filesystem_write = false,
        allow_subprocess = false, # verification probes may shell out (e.g. grep, test -f)
      },
      metadata = {
        name = "must-runner",
        version = "1.0.0",
        description = "Evaluates every invariant in the adjacent must.k9.ncl declaration as a hard gate.",
        paired_xfile = "must.k9.ncl#declaration",
        author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
      },
    },

  # Contract schema — the shape every must declaration (must.k9.ncl `declaration`) targets.
  # Used by `contractile must typecheck`.
  schema = {
    invariants
      | Array {
        id | String,
        description | String,
        # TODO: migrate to base.probe_schema (structured probe) when CLI supports it
        probe | String, # shell command; exit 0 = pass
        # status_core values: 'declared, 'verified, 'failing
        status | [| 'declared, 'verified, 'failing |] | default = 'declared,
        severity | [| 'critical, 'high, 'medium |] | default = 'critical,
        notes | String | optional,
        fix | String | optional,
      },
  },

  # Runner behaviour — consumed by the contractile CLI dispatcher.
  # Inherits from base.run_defaults; on_any_fail is the hard-gate default.
  run =
    base.run_defaults
    & {
      on_any_fail = "exit-nonzero", # hard gate
      report_format = "json",
      emit_summary = true,
    },
}
