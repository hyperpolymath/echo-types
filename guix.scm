;; SPDX-License-Identifier: MPL-2.0
;; Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
;;
;; Guix development environment for echo-types. Replaces flake.nix (Guix-only policy).
;; Usage: guix shell -D -f guix.scm
(use-modules (guix packages) (guix build-system gnu))
(package
  (name "echo-types") (version "0.1.0") (source #f)
  (build-system gnu-build-system)
  (synopsis "echo-types") (description "echo-types — part of the hyperpolymath ecosystem.")
  (home-page "https://github.com/hyperpolymath/echo-types")
  (license ((@@ (guix licenses) license) "MPL-2.0" "https://github.com/hyperpolymath/palimpsest-license")))
