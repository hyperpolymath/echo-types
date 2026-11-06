K9!
# SPDX-License-Identifier: MPL-2.0
# Thin coordination bindings for central session-management standards

{
  pedigree = {
    schema_version = "1.0.0",
    component_type = "session:coordination-binding",
    metadata = {
      name = "echo-types-session-coordination",
      version = "1.0.0",
      description = "Pointers to canonical session protocols; no executable grant.",
    },
    security = {
      leash = 'Kennel,
      allow_network = false,
      allow_filesystem_write = false,
      allow_subprocess = false,
      signature_required = false,
    },
  },

  session_management = {
    source_of_truth = "https://github.com/metadatastician/standards/tree/ba640e9a57f22608710ffecdca282074eac55a0b/3-practice/session-management-standards",
    canonical_commands = [
      "intake repo <path>",
      "checkpoint change <path>",
      "verify maintenance <path>",
      "verify substantial <path>",
      "verify release <path>",
      "close planned <path>",
      "close urgent <path>",
      "recover repo <path>",
      "handover full <path>",
      "handover split <path>",
      "handover model <path>",
      "handover human <path>",
    ],
  },

  signals = [
    { name = "session.intake", command = "intake repo <path>" },
    { name = "session.checkpoint", command = "checkpoint change <path>" },
    { name = "session.verify.maintenance", command = "verify maintenance <path>" },
    { name = "session.verify.substantial", command = "verify substantial <path>" },
    { name = "session.verify.release", command = "verify release <path>" },
    { name = "session.close.planned", command = "close planned <path>" },
    { name = "session.close.urgent", command = "close urgent <path>" },
    { name = "session.recover", command = "recover repo <path>" },
    { name = "session.handover.full", command = "handover full <path>" },
    { name = "session.handover.split", command = "handover split <path>" },
    { name = "session.handover.model", command = "handover model <path>" },
    { name = "session.handover.human", command = "handover human <path>" },
  ],
}
