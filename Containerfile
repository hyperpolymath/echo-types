# SPDX-License-Identifier: PMPL-1.0-or-later
# Containerfile — podman-build fallback when stapeln is unavailable.

# TODO(scaffold): pin @sha256
FROM cgr.dev/chainguard/wolfi-base:latest AS build

USER root
RUN apk add --no-cache agda ghc cabal

WORKDIR /build
COPY echo-types.agda-lib ./
COPY proofs ./proofs

RUN agda -i proofs/agda proofs/agda/All.agda

FROM cgr.dev/chainguard/static:latest AS runtime
USER nonroot

COPY --from=build /build/proofs /app/proofs
COPY --from=build /build/echo-types.agda-lib /app/echo-types.agda-lib

ENTRYPOINT ["/bin/sh", "-c", "echo 'echo-types is a proof-artefact carrier; mount /app/proofs into your downstream Agda project.'"]
