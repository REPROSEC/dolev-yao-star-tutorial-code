{lib, stdenv, which, fstar, z3, ocamlPackages, comparse, dolev-yao-star, fetchFromGitHub}:

let
  dolev-yao-star-tutorial = stdenv.mkDerivation {
    name = "dolev-yao-star-tutorial";
    src =
      lib.sources.sourceByRegex ./. [
        "Makefile"
        "dy-extensions(/.*)?"
        "examples(/.*)?"
      ]
    ;
    enableParallelBuilding = true;
    buildInputs = [ which fstar z3 ];
    COMPARSE_HOME = comparse;
    DY_HOME = dolev-yao-star;
    # pre-patch uses build output from dolev-yao-star, to avoid building things twice
    prePatch = ''
      cp -pr --no-preserve=mode ${dolev-yao-star}/cache ${dolev-yao-star}/ml .
      mkdir obj
      cp -p ml/lib/src/* obj/
    '';
    installPhase = ''
      mkdir -p $out
      cp -r ml dy-extensions examples cache hints $out
    '';
    passthru.tests = dolev-yao-star-tutorial-tests;
  };
  dolev-yao-star-tutorial-tests = stdenv.mkDerivation {
    name = "dolev-yao-star-tutorial-tests";
    src =
      lib.sources.sourceByRegex ./. [
        "Makefile"
        "dy-extensions(/.*)?"
        "examples(/.*)?"
      ]
    ;
    # parallel builds messes up with .depend... to fix
    enableParallelBuilding = false;
    buildInputs =
      [ which fstar z3 ]
      ++ (with ocamlPackages; [
        ocaml ocamlbuild findlib #dune_3
      ])
      ++ (fstar.buildInputs);
    COMPARSE_HOME = comparse;
    DY_HOME = dolev-yao-star;
    # pre-patch uses build output from dolev-yao-star, to avoid building things twice
    prePatch = ''
      cp -pr --no-preserve=mode ${dolev-yao-star-tutorial}/cache ${dolev-yao-star-tutorial}/ml .
      mkdir obj
      cp -p ml/lib/src/* obj/
    '';
    doCheck = true;
    installPhase = ''
      touch $out
    '';
  };
in
  dolev-yao-star-tutorial
