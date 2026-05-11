# Security Policy

## Reporting a Vulnerability

Email `j.d.a.jewell@open.ac.uk` with subject `[security] echo-types: <summary>`.
PGP key fingerprint published at the hyperpolymath organisation profile.

Expect an acknowledgement within 72 hours and an initial assessment within 7 days.

## Supported Versions

| Version | Supported |
|---------|-----------|
| Latest tagged release | Yes |
| Previous minor       | 90 days from successor release |
| All older versions   | No |

## Security Posture

This is a formal-methods library:

* Constructive Agda proofs (no postulates in the load-bearing tracks).
* No `believe_me` in distinctness arguments. CI checks for these patterns.
* Imports are pinned in `echo-types.agda-lib`; updates are reviewed.
* Container images use Chainguard distroless bases (when `stapeln.toml` lands a green build).

There is no networked attack surface — echo-types is a proof library, not a service. Report concerns about proof soundness to the same address as security issues.
