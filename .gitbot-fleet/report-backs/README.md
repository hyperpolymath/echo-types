<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
# Fleet report-backs

This directory intentionally contains no committed report-back JSON. The read-only producer pinned at gitbot-fleet `34908580b98cd354caa3bfc5a000bc7935957fce` writes per-run `<member>.json` envelopes to the `fleet-report-backs` artifact; the consumer renders those envelopes with the checked source revision.

[../enrolment.json](../enrolment.json) declares applicability, not permission to remediate, commit, push, or certify proofs. Rhodibot, finishingbot, and glambot are enrolled for this Agda/documentation repository. Other members carry explicit reasons for non-enrolment; Agda proofs remain present even though no ECHIDNA engine integration is configured.

A successful producer job means the report-back driver completed, not that every adapter succeeded or that the repository passed. Missing, failed, or unreadable evidence must retain its reported status. Do not commit generated envelopes or substitute an empty successful report for a missing scan.
