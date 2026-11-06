# SPDX-License-Identifier: MPL-2.0
# Canonical bust schema/run-policy data adapted for echo-types.
# This expression does not execute probes; root recipes execute checks.
let base = import "../_base.ncl" in

{
  pedigree =
    base.pedigree_schema
    & {
      contractile_verb = "bust",
      semantics = "error handling + failure recovery",
      security = {
        leash = 'Kennel,
        trust_level = "controlled failure injection; scoped to system-under-test",
        allow_network = false,
        allow_filesystem_write = true, # drills may write transient state (tmp dirs, test DBs)
        allow_subprocess = false,
        injection_scope = "system-under-test-only",
      },
      metadata = {
        name = "bust-runner",
        version = "1.0.0",
        description = "Exercises declared failure modes and verifies recovery paths. Hard-gates on any failure mode without working recovery.",
        paired_xfile = "bust.k9.ncl#declaration",
        author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
      },
    },

  schema = {
    failure_modes
      | Array {
        id | String,
        description | String,
        class | [| 'network, 'disk_full, 'oom, 'timeout, 'partial_write, 'panic, 'crash, 'rollback, 'concurrency |],
        # TODO: migrate to base.probe_schema (structured probe) when CLI supports it
        injection_probe | String, # command that deterministically causes this failure
        # TODO: migrate to base.probe_schema (structured probe) when CLI supports it
        recovery_probe | String, # command that verifies recovery (exit 0 = recovered)
        expected_recovery_time_seconds | Number | default = 30,
        # status_core values: 'declared, 'verified, 'failing; bust adds 'drilled
        status | [| 'declared, 'drilled, 'verified, 'failing |] | default = 'declared,
        notes | String | optional,
      },
  },

  # Runner behaviour — inherits from base.run_defaults.
  # bust adds record_recovery_times for performance tier feeding.
  run =
    base.run_defaults
    & {
      on_any_fail = "exit-nonzero", # missing or broken recovery blocks merge
      report_format = "json",
      emit_summary = true,
      record_recovery_times = true, # feeds the performance tier
    },
}
