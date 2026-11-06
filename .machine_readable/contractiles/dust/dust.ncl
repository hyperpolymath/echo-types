# SPDX-License-Identifier: MPL-2.0
# Canonical dust schema/run-policy data adapted for echo-types.
# This expression does not execute probes; root recipes execute checks.
let base = import "../_base.ncl" in

{
  pedigree =
    base.pedigree_schema
    & {
      contractile_verb = "dust",
      semantics = "exnovation / removal",
      security = {
        leash = 'Kennel,
        trust_level = "proposes deletion; --apply required to execute",
        allow_network = false,
        allow_filesystem_write = true, # --apply mode writes (deletes)
        allow_subprocess = false,
        destructive_mode_requires_flag = "--apply",
      },
      metadata = {
        name = "dust-runner",
        version = "1.0.0",
        description = "Identifies and optionally removes exnovation targets listed in the dust.k9.ncl declaration. Destructive mode gated behind --apply.",
        paired_xfile = "dust.k9.ncl#declaration",
        author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
      },
    },

  schema = {
    removal_candidates
      | Array {
        id | String,
        description | String,
        target | String, # file / path / symbol / dep name
        reason | String, # why it's a removal candidate
        # TODO: migrate to base.probe_schema (structured probe) when CLI supports it
        probe | String | optional, # command that confirms it's still removable
        # dust has a non-standard status progression (no 'verified):
        #   'declared → 'proposed → 'approved → 'removed
        status | [| 'declared, 'proposed, 'approved, 'removed |] | default = 'declared,
        approver | String | optional, # who signed off (for 'approved / 'removed)
        notes | String | optional,
      },
  },

  # Runner behaviour — inherits from base.run_defaults.
  # dust is advisory; apply_requires_approval is dust-specific.
  run =
    base.run_defaults
    & {
      on_any_fail = "continue-with-warnings",
      report_format = "json",
      emit_summary = true,
      apply_requires_approval = true, # only 'approved items get swept, even with --apply
    },
}
