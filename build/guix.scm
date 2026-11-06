;; SPDX-License-Identifier: MPL-2.0
;; Development prerequisites, not a distributable echo-types package.
;; Usage: guix shell -m build/guix.scm -- bash
;; Then follow docs/build.adoc to install the checksum-pinned Agda toolchain.
;; Syntax: GNU Guix manual, "Writing Manifests" and "Invoking guix shell".
;; https://guix.gnu.org/manual/en/html_node/Writing-Manifests.html
;; Package versions follow the caller's Guix channel; no channel is pinned here.

(use-modules (gnu packages))

(specifications->manifest
 '("bash"
   "coreutils"
   "curl"
   "git-minimal"
   "nss-certs"
   "tar"
   "xz"
   "findutils"
   "grep"
   "sed"
   "gawk"))
