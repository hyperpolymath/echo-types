{
  # SPDX-License-Identifier: MPL-2.0
  #
  # Development environment for echo-types. Consumed by .envrc (`use flake`).
  # Toolchain mirrors .tool-versions (cabal / rust / just) plus Agda, which
  # the Justfile and echo-types.agda-lib require.
  #
  # nixpkgs pinned to nixos-24.11: rustc 1.82.0 + cabal-install 3.12.1.0
  # (exact .tool-versions match), agda 2.7.0.1, ghc 9.6.6, just 1.38.0.
  #
  # Agda library resolution (echo-types.agda-lib: depend standard-library
  # absolute-zero): standard-library comes from nixpkgs (reproducible);
  # absolute-zero has no usable upstream package, so the local checkout at
  # ~/dev/repos/absolute-zero is registered via a generated AGDA libraries
  # file in the shellHook. Clone github.com/hyperpolymath/absolute-zero there
  # if missing.
  description = "echo-types dev shell (Agda + Haskell + Rust + just)";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.11";

  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAllSystems = nixpkgs.lib.genAttrs systems;
    in {
      devShells = forAllSystems (system:
        let
          pkgs = import nixpkgs { inherit system; };
          stdlib = pkgs.agdaPackages.standard-library;
        in {
          default = pkgs.mkShell {
            name = "echo-types";
            packages = [
              pkgs.agda
              pkgs.just
              pkgs.ghc
              pkgs.cabal-install
              pkgs.rustc
              pkgs.cargo
              pkgs.rustfmt
              pkgs.clippy
            ];
            shellHook = ''
              # Agda library file: nixpkgs standard-library (reproducible) +
              # local absolute-zero checkout (no usable upstream package).
              export AGDA_DIR="$PWD/.agda"
              mkdir -p "$AGDA_DIR"
              _stdlib_agdalib="$(echo ${stdlib}/*.agda-lib)"
              _az="$HOME/dev/repos/absolute-zero/absolute-zero.agda-lib"
              {
                echo "$_stdlib_agdalib"
                [ -f "$_az" ] && echo "$_az"
              } > "$AGDA_DIR/libraries"

              echo "echo-types devShell ready"
              command -v agda  >/dev/null && echo "  agda : $(agda --version 2>/dev/null | head -n1)"
              command -v just  >/dev/null && echo "  just : $(just --version 2>/dev/null)"
              command -v rustc >/dev/null && echo "  rustc: $(rustc --version 2>/dev/null)"
              command -v cabal >/dev/null && echo "  cabal: $(cabal --version 2>/dev/null | head -n1)"
              if [ -f "$_az" ]; then
                echo "  agda libs: standard-library + absolute-zero (local)"
              else
                echo "  WARNING: absolute-zero NOT found at $_az" >&2
                echo "           clone github.com/hyperpolymath/absolute-zero into ~/dev/repos" >&2
                echo "  agda libs: standard-library only (absolute-zero MISSING)"
              fi
            '';
          };
        });
    };
}