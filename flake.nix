{
  inputs = {
    nixpkgs.follows = "dolev-yao-star-flake/nixpkgs";
    fstar-flake.follows = "dolev-yao-star-flake/fstar-flake";
    comparse-flake.follows = "dolev-yao-star-flake/comparse-flake";
    dolev-yao-star-flake.url = "github:REPROSEC/dolev-yao-star-extrinsic";
  };

  outputs = {self, nixpkgs, fstar-flake, comparse-flake, dolev-yao-star-flake}:
  let
    system = "x86_64-linux";
    pkgs = import nixpkgs { inherit system; };
    z3 = fstar-flake.packages.${system}.z3;
    fstar = fstar-flake.packages.${system}.fstar;
    fstar-dune = fstar-flake.packages.${system}.fstar-dune;
    comparse = comparse-flake.packages.${system}.comparse;
    dolev-yao-star = dolev-yao-star-flake.packages.${system}.dolev-yao-star;
    dolev-yao-star-tutorial = pkgs.callPackage ./default.nix {inherit fstar fstar-dune z3 comparse dolev-yao-star; ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;};
  in {
    packages.${system} = {
      default = dolev-yao-star-tutorial;
      inherit dolev-yao-star-tutorial;
    };
    devShells.${system}.default = pkgs.mkShell {
      packages = [
        fstar z3
      ] ++ (with pkgs.ocaml-ng.ocamlPackages_4_14; [
        ocaml dune_3 findlib yojson
      ])
      ++ (fstar.buildInputs);
    };
    checks.${system} = {
      dolev-yao-star-tutorial-build = dolev-yao-star-tutorial;
      dolev-yao-star-tutorial-tests = dolev-yao-star-tutorial.tests;
    };
  };
}
