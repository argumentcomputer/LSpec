{
  description = "Lean 4 Example Project";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-24.11";
    flake-parts.url = "github:hercules-ci/flake-parts";
    lean4-nix = {
      url = "github:argumentcomputer/lean4-nix";
      inputs.nixpkgs.follows = "nixpkgs";
      #rev = "";
    };
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

      flake = {
        lib = import ./lspec.nix;
      };

      perSystem = {
        system,
        pkgs,
        self',
        config,
        ...
      }:
        let
          lib = (import ./lspec.nix { inherit pkgs lean4-nix; }).lib;
          lspecBin = lib.lspecLib.executable;
        in
      {
        _module.args.pkgs = import nixpkgs {
          inherit system;
          overlays = [(lean4-nix.readToolchainFile ./lean-toolchain)];
        };
        # TODO: Replace with a Nix-compatible binary
        # Running `lspecBin` will cause an error due to calling `lake` explicitly and only parsing `lakefile.lean` files
        # It is included for completeness only
        #packages.default = lspecBin;

        devShells.default = pkgs.mkShell {
          packages = with pkgs.lean; [lean lean-all];
        };
    };
  };
}
