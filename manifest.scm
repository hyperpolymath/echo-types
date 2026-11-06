;;; SPDX-License-Identifier: MPL-2.0
;;; Compatibility entrypoint for the primary development manifest.
;;; Usage: guix shell -m manifest.scm -- bash
;;; Keep the package list and its limitations in build/guix.scm.

(load (string-append (dirname (current-filename)) "/build/guix.scm"))
