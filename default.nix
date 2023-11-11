{ # Is this a nix-shell invocation?
  inNixShell ? false
  # Do we want the full Agda package for interactive use? Set to false in CI
, interactive ? true
, system ? builtins.currentSystem
}:
let
  pkgs = import ./support/nix/nixpkgs.nix { inherit system; };
  inherit (pkgs) lib;

  our-ghc = pkgs.labHaskellPackages.ghcWithPackages (ps: with ps; ([
    shake directory tagsoup
    text containers uri-encode
    process aeson Agda pandoc SHA
    fsnotify
  ] ++ (if interactive then [ haskell-language-server ] else [])));

  our-texlive = pkgs.texlive.combine {
    inherit (pkgs.texlive)
      collection-basic
      collection-latex
      xcolor
      preview
      pgf tikz-cd
      mathpazo
      varwidth xkeyval standalone;
  };

  shakefile = pkgs.callPackage ./support/nix/build-shake.nix {
    inherit our-ghc;
    name = "1lab-shake";
    main = "Main.hs";
  };

  deps = with pkgs; [
    # For driving the compilation:
    shakefile

    # For building the text and maths:
    gitMinimal sassc

    # For building diagrams:
    poppler_utils our-texlive
  ] ++ (if interactive then [
    our-ghc
  ] else [
    labHaskellPackages.Agda.data
    labHaskellPackages.pandoc.data
  ]);
in
  pkgs.stdenv.mkDerivation rec {
    name = "1lab";

    src = if inNixShell then null else
      with pkgs.nix-gitignore; gitignoreFilterSourcePure (_: _: true) [
        # Keep .git around for extracting page authors
        (compileRecursiveGitignore ./.)
        ".github"
      ] ./.;

    nativeBuildInputs = deps;

    shellHook = ''
      export out=_build/site
    '';

    LANG = "C.UTF-8";
    buildPhase = ''
      1lab-shake all -j
    '';

    installPhase = ''
      # Copy our build artifacts
      mkdir -p $out
      cp -Lrvf _build/html/* $out

      # Copy KaTeX CSS and fonts
      mkdir -p $out/css
      cp -Lrvf --no-preserve=mode ${pkgs.nodePackages.katex}/lib/node_modules/katex/dist/{katex.min.css,fonts} $out/css/
      mkdir -p $out/static/ttf
      cp -Lrvf --no-preserve=mode ${pkgs.julia-mono}/share/fonts/truetype/JuliaMono-Regular.ttf $out/static/ttf/julia-mono.ttf
    '';

    passthru = {
      inherit deps shakefile;
      texlive = our-texlive;
      ghc = our-ghc;

      sort-imports = let
        script = builtins.readFile support/sort-imports.hs;
        # Extract the list of dependencies from the stack shebang comment.
        deps = lib.concatLists (lib.filter (x: x != null)
          (map (builtins.match ".*--package +([^[:space:]]*).*")
            (lib.splitString "\n" script)));
      in pkgs.writers.writeHaskellBin "sort-imports" {
        ghc = pkgs.labHaskellPackages.ghc;
        libraries = lib.attrVals deps pkgs.labHaskellPackages;
      } script;
    };
  }
