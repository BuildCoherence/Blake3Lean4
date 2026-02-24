{
  description = "Blake3Lean4: A standalone Lean 4 implementation of BLAKE3";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    blake3-repo = {
      url = "github:BLAKE3-team/BLAKE3";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, blake3-repo }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in {
        devShells.default = pkgs.mkShell {
          nativeBuildInputs = [
            pkgs.elan
          ];
          BLAKE3_TEST_VECTORS = "${blake3-repo}/test_vectors/test_vectors.json";
        };
      });
}
