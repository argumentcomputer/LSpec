{pkgs, lean4-nix}:
let
  # Creates a Lean package for LSpec
  lspecLib = ((lean4-nix.lake {inherit pkgs;}).mkPackage {
    name = "LSpec";
    src = ./.;
    roots = ["Main" "LSpec"];
  });

  # Extracts test names from the lakefile
  extractTestNames = src: pkgs.runCommand "extract-test-names" {
    buildInputs = [ pkgs.gnused pkgs.gnugrep ];
  } ''
    if [ ! -f ${src}/lakefile.lean ]; then
      echo "Error: lakefile.lean not found" >&2
      exit 1
    fi

    grep -o "lean_exe Tests\.[^ ]*" ${src}/lakefile.lean | \
      sed 's/lean_exe Tests\.//' > $out
  '';

  # Reads the test names into a Nix list
  testNames = src:
    let
      content = builtins.readFile (extractTestNames src);
      # Split the content by newlines
      splitResult = builtins.split "\n" content;
      # Filter to only keep the string elements
      isString = x: builtins.typeOf x == "string";
      # Keep only non-empty strings
      nonEmptyStrings = builtins.filter (x: isString x && x != "") splitResult;
    in
      nonEmptyStrings;

  # Generates test packages for each test in the lakefile
  mkTests = src: pkgs.lib.genAttrs (testNames src) (name: ((lean4-nix.lake {inherit pkgs;}).mkPackage {
    inherit name src;
    roots = ["Tests.${name}"];
    deps = [ lspecLib ];
  }).executable);

  # Runs each test package, replicating `lake exe lspec`
  allTests = src:
    let
      tests = mkTests src;
      testNames = pkgs.lib.attrNames tests;
    in
    pkgs.writeShellApplication {
      name = "all-tests";
      runtimeInputs = pkgs.lib.attrValues tests;
      text = ''
        #!/usr/bin/env bash
        set -euo pipefail

        echo "Running all tests:"

        ${pkgs.lib.concatMapStringsSep "\n" (string: ''
          echo "Running ${string}..."
          ${tests.${string}}/bin/${pkgs.lib.toLower string}
        '') testNames }

        echo "All tests executed successfully"
      '';
    };

  lib = {
    inherit
      lspecLib
      extractTestNames
      testNames
      mkTests
      allTests;
  };
in
{
  inherit lib;
}
