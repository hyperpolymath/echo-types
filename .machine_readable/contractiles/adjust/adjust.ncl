# SPDX-License-Identifier: MPL-2.0
# Canonical adjust schema/run-policy data adapted for echo-types.
# This expression does not execute probes; root recipes execute checks.
let base = import "../_base.ncl" in

{
  pedigree =
    base.pedigree_schema
    & {
      contractile_verb = "adjust",
      semantics = "accessibility compliance",
      security = {
        leash = 'Kennel,
        trust_level = "fixes allowed where deterministic",
        allow_network = false,
        allow_filesystem_write = true, # `adjust fix` may write (deterministic patches only)
        allow_subprocess = false,
      },
      metadata = {
        name = "adjust-runner",
        version = "1.0.0",
        description = "Evaluates accessibility requirements from the adjust.k9.ncl declaration. Fixes deterministic items; flags the rest for human review.",
        paired_xfile = "adjust.k9.ncl#declaration",
        author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
      },
    },

  schema = {
    requirements
      | Array {
        id | String,
        description | String,
        # TODO: migrate to base.probe_schema (structured probe) when CLI supports it
        probe | String,
        # status_core values: 'declared, 'verified, 'failing; adjust adds 'partial
        status | [| 'declared, 'partial, 'verified, 'failing |] | default = 'declared,
        compliance | String | optional, # e.g. "WCAG 2.1 AA"
        notes | String | optional,
        fix | String | optional, # deterministic fix command (optional)
      },
  },

  # Runner behaviour — inherits from base.run_defaults.
  # adjust is advisory (continue-with-warnings) not a hard gate.
  # auto_fix_when_available is adjust-specific.
  run =
    base.run_defaults
    & {
      on_any_fail = "continue-with-warnings", # accessibility is progress-tracked, not a hard gate by default
      report_format = "json",
      emit_summary = true,
      auto_fix_when_available = false,
    },
}
