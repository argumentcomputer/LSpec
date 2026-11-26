{
  description = "LSpec Nix Flake";

  nixConfig = {
    extra-substituters = [
      "https://argumentcomputer.cachix.org"
    ];
    extra-trusted-public-keys = [
      "argumentcomputer.cachix.org-1:ovhbTx1V56BYDerOWInQvXKXl68LlhNwEA+n7EWk1m4="
    ];
  };

  inputs = {
    nixpkgs.follows = "lean4-nix/nixpkgs";
    flake-parts.url = "github:hercules-ci/flake-parts";
    lean4-nix.url = "github:argumentcomputer/lean4-nix";
  };

  outputs = inputs @ {
    flake-parts,
    lean4-nix,
    ...
  }:
    flake-parts.lib.mkFlake {inherit inputs;} {
      systems = [
        "aarch64-darwin"
        "aarch64-linux"
        "x86_64-darwin"
        "x86_64-linux"
      ];

      perSystem = {
        system,
        pkgs,
        ...
      }: let
        lean = lean4-nix.lib.${system}.fromToolchainFile ./lean-toolchain;
        lake2nix = pkgs.callPackage lean4-nix.lake {inherit lean;};

        # Restrict the build inputs to the files `lake build` reads, so edits
        # to the flake, CI config, or docs don't invalidate the build.
        src = lake2nix.cleanLakeSource ./.;

        # Library build, shared between the package output and the test check
        # so the `tests` exe reuses these artifacts instead of recompiling them.
        lspec = lake2nix.mkPackage {
          name = "LSpec";
          inherit src;
        };

        # `mkPackage "LSpec"` only builds the library target, so the `tests`
        # exe and `LSpecProofs` library are built explicitly, reusing `lspec`'s
        # build artifacts.
        lspecTest = lake2nix.mkPackage {
          name = "tests";
          inherit src;
          lakeArtifacts = lspec;
        };

        lspecProofs = lake2nix.mkPackage {
          name = "LSpecProofs";
          inherit src;
          lakeArtifacts = lspec;
        };
      in {
        # Build the library with `nix build`
        packages.default = lspec;

        # Build and run the test suite and verify formal proofs (`nix flake check`).
        checks.tests = pkgs.runCommand "LSpec-tests" {} ''
          ${lspecTest}/bin/tests
          touch $out
        '';

        checks.proofs = lspecProofs;

        devShells.default = pkgs.mkShell {
          packages = [lean];
        };
      };
    };
}
