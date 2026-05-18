{
  # SPDX-License-Identifier: PMPL-1.0-or-later
  #
  # Reproducible toolchain for echo-types — foundation P1 (CI-via-flake
  # exact pin; docs/foundation.adoc §"Known limitations").
  #
  # CROSS-STACK NOTE. A simpler devShell-only flake.nix also exists on
  # the reframe stack (commit 185eb74, PR #47). THIS file is a strict
  # evolution of it (same devShell tools + PINNED Agda-library inputs +
  # a hermetic `checks` output). At integration, this harden-stack
  # version supersedes the reframe-stack one — no behavioural conflict,
  # it only adds pins and checks.
  #
  # PINNING DECISION (explicit, surfaced — not assumed):
  #   * Agda: nixpkgs `nixos-24.11` -> agda 2.7.0.1 (also ghc 9.6.6,
  #     cabal 3.12.1.0, rustc 1.82.0, just 1.38.0 — .tool-versions
  #     match). The verified-green local toolchain is agda 2.8.0; CI's
  #     apt job runs yet another. The suite has so far proven robust
  #     across apt-agda and 2.8.0; whether it also typechecks under
  #     2.7.0.1 + stdlib v2.3 is VERIFIED BY the additive
  #     `nix flake check` CI job, not assumed here. If that job is red
  #     it surfaces the exact version delta to reconcile (bump the
  #     nixpkgs input); the apt + cold-check jobs remain the gate
  #     meanwhile, so nothing regresses.
  #   * standard-library: PINNED to tag v2.3 as a flake input (was
  #     nixpkgs-bundled — a different version than CI/local verify).
  #   * absolute-zero: PINNED to commit 3ff5cee… as a flake input
  #     (was a local ~/dev checkout — not reproducible / not CI-usable).
  #
  # NOTE: authored without a local `nix` (none in the dev env);
  # flake.lock is generated and the build first verified BY CI.
  # Designed-correct, CI-verified — not locally claimed green.
  description = "echo-types reproducible toolchain (Agda + libs pinned)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.11";
    agda-stdlib = {
      url = "github:agda/agda-stdlib/v2.3";
      flake = false;
    };
    absolute-zero = {
      url = "github:hyperpolymath/absolute-zero/3ff5cee7f3fd002378089cd02f0c90a3747b45f0";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, agda-stdlib, absolute-zero }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAllSystems = nixpkgs.lib.genAttrs systems;

      # The Agda libraries file as an exact store file — no heredoc,
      # no Nix-string indentation hazard. Agda resolves each
      # `.agda-lib`'s `include:` relative to that file's own directory,
      # so pointing at the pinned inputs' own `.agda-lib` paths is
      # sufficient. (Nix `"..."` interprets `\n` as a real newline.)
      mkLibs = pkgs: pkgs.writeText "agda-libraries"
        "${agda-stdlib}/standard-library.agda-lib\n${absolute-zero}/absolute-zero.agda-lib\n";
    in {
      devShells = forAllSystems (system:
        let
          pkgs = import nixpkgs { inherit system; };
          libs = mkLibs pkgs;
        in {
          default = pkgs.mkShell {
            name = "echo-types";
            packages = [
              pkgs.agda pkgs.just pkgs.ghc pkgs.cabal-install
              pkgs.rustc pkgs.cargo pkgs.rustfmt pkgs.clippy
            ];
            shellHook = ''
              export AGDA_DIR="$PWD/.agda"
              mkdir -p "$AGDA_DIR"
              cp -f ${libs} "$AGDA_DIR/libraries"
              chmod u+w "$AGDA_DIR/libraries"
              echo "echo-types devShell (PINNED):"
              command -v agda >/dev/null && echo "  agda  : $(agda --version 2>/dev/null | head -n1)"
              echo "  stdlib: v2.3 (flake input, pinned)"
              echo "  absz  : 3ff5cee (flake input, pinned)"
            '';
          };
        });

      # Hermetic, reproducible verification: the flake-pinned Agda over
      # the pinned stdlib v2.3 + absolute-zero, running the same
      # guardrail + four roots + N5 expected-failure gate that CI's
      # apt job runs. `nix flake check` exercises this.
      checks = forAllSystems (system:
        let
          pkgs = import nixpkgs { inherit system; };
          libs = mkLibs pkgs;
        in {
          suite = pkgs.runCommand "echo-types-suite"
            { nativeBuildInputs = [ pkgs.agda pkgs.bash ]; }
            ''
              export HOME="$TMPDIR"
              mkdir -p "$HOME/.agda"
              cp -f ${libs} "$HOME/.agda/libraries"
              # Agda needs a writable source tree (.agdai outputs).
              cp -r ${self} src
              chmod -R u+w src
              cd src
              bash tools/check-guardrails.sh proofs/agda
              agda -i proofs/agda proofs/agda/All.agda
              agda -i proofs/agda proofs/agda/Smoke.agda
              agda -i proofs/agda proofs/agda/characteristic/All.agda
              agda -i proofs/agda proofs/agda/examples/All.agda
              if agda -i proofs/agda proofs/agda/characteristic/N5Falsifier.agda \
                   > /dev/null 2>&1; then
                echo "N5Falsifier unexpectedly typechecks — see foundation.adoc"
                exit 1
              fi
              touch "$out"
            '';
        });
    };
}
