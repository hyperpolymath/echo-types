# SPDX-License-Identifier: MPL-2.0
# Canonical intend schema/run-policy data adapted for echo-types.
# This expression does not execute probes; root recipes execute checks.
let base = import "../_base.ncl" in

{
  pedigree =
    base.pedigree_schema
    & {
      contractile_verb = "intend",
      semantics = "north-star (commitments + aspirations)",
      security = {
        leash = 'Kennel,
        trust_level = "read-only reporting",
        allow_network = false,
        allow_filesystem_write = false,
        allow_subprocess = false, # probe commands may shell out (intents only; wishes never probe)
      },
      metadata = {
        name = "intend-runner",
        version = "2.0.0",
        description = "Reports progress toward committed next-actions and lists horizon aspirations. Non-gating. Absorbed `lust` semantics 2026-04-18.",
        paired_xfile = "intend.k9.ncl#declaration",
        author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
      },
    },

  schema = {
    intents
      | Array {
        id | String,
        description | String,
        # TODO: migrate to base.probe_schema (structured probe) when CLI supports it
        probe | String | optional, # shell command that indicates done-ness
        status | [| 'declared, 'in_progress, 'done, 'deferred, 'retired |] | default = 'declared,
        notes | String | optional,
        target_date | String | optional,
      },
    wishes
      | Array {
        id | String,
        description | String,
        horizon | [| 'near, 'mid, 'far |] | default = 'mid,
        why | String | optional,
        status | [| 'declared, 'in_progress, 'achieved, 'abandoned |] | default = 'declared,
        notes | String | optional,
      }
      | optional,
  },

  # Runner behaviour — inherits from base.run_defaults.
  # intend never blocks; it is a report only.
  # emit_diff is intent-specific (declared vs observed probes).
  # emit_grouped_by_horizon renders wishes grouped by near/mid/far.
  run =
    base.run_defaults
    & {
      on_pass = "continue",
      on_any_fail = "continue", # never blocks; it's a report
      report_format = "json",
      emit_summary = true,
      emit_diff = true, # declared vs observed (intents)
      emit_grouped_by_horizon = true, # wishes grouped by horizon (absorbed from lust)
    },
}
