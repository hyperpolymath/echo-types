# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# Rootless Podman fallback: verify All with the same pinned compiler/libraries as CI.
FROM cgr.dev/chainguard/wolfi-base@sha256:0efdcacdc6ab6d4f00507f1c0aa35e6bcbd50f838a45fe560e0e3b12056e3181 AS build

# Package provisioning needs the base image's build-time administrator. Proof
# downloads, checking and the delivered carrier run as an unprivileged user.
RUN apk add --no-cache bash curl git xz coreutils ca-certificates && mkdir -p /build && chown 65532:65532 /build
USER 65532:65532
WORKDIR /build
ENV HOME=/build AGDA_TOOLS_DIR=/build/toolchain
COPY --chown=65532:65532 scripts/setup-agda.sh ./scripts/setup-agda.sh
RUN bash scripts/setup-agda.sh
COPY --chown=65532:65532 echo-types.agda-lib ./
COPY --chown=65532:65532 proofs ./proofs
RUN bash -c 'source "$AGDA_TOOLS_DIR/env.sh"; agda --safe --without-K --cubical-compatible --no-libraries -i proofs/agda -i "$AGDA_STDLIB" -i "$ABSOLUTE_ZERO_AGDA" proofs/agda/All.agda'

# The carrier has a real shell for its informational entrypoint. It is not a
# service and does not bundle the compiler or claim all proof roots were checked.
FROM cgr.dev/chainguard/wolfi-base@sha256:0efdcacdc6ab6d4f00507f1c0aa35e6bcbd50f838a45fe560e0e3b12056e3181 AS runtime
USER 65532:65532
COPY --from=build /build/proofs /app/proofs
COPY --from=build /build/echo-types.agda-lib /app/echo-types.agda-lib
ENTRYPOINT ["/bin/sh", "-c", "printf '%s\n' 'Echo Types proof-source carrier: All.agda checked with Agda 2.7.0.1. Recheck with the documented pinned libraries before downstream use.'"]
