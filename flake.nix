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
    lean4-nix.url = "github:lenianiva/lean4-nix";
  };

  outputs = inputs @ {
    nixpkgs,
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
        self',
        config,
        ...
      }: let
        lake2nix = pkgs.callPackage lean4-nix.lake {};

        # Library build, shared between the package output and the test check
        # so the `tests` exe reuses these artifacts instead of recompiling them.
        lspec = lake2nix.mkPackage {
          name = "LSpec";
          src = ./.;
        };

        # `mkPackage "LSpec"` only builds the library target, so the `tests`
        # exe is built explicitly, reusing `lspec`'s build artifacts.
        lspecTest = lake2nix.mkPackage {
          name = "tests";
          src = ./.;
          lakeArtifacts = lspec;
        };
      in {
        _module.args.pkgs = import nixpkgs {
          inherit system;
          overlays = [(lean4-nix.readToolchainFile ./lean-toolchain)];
        };

        # Build the library with `nix build`
        packages.default = lspec;

        # Build and run the test suite as a flake check (`nix flake check`).
        checks.tests = pkgs.runCommand "LSpec-tests" { } ''
          ${lspecTest}/bin/tests
          touch $out
        '';

        devShells.default = pkgs.mkShell {
          packages = with pkgs.lean; [lean-all];
        };
      };
    };
}
