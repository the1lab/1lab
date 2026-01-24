{ # Is this a nix-shell invocation?
  # NOTE: We do not rely on the IN_NIX_SHELL environment variable as it
  # also affects nix-build invocations inside of nix shells.
  inNixShell ? false
  # Do we want the full Agda package for interactive use? Set to false in CI
, interactive ? inNixShell
, system ? builtins.currentSystem
}:
let
  pkgs = import ./support/nix/nixpkgs.nix { inherit system; };
  inherit (pkgs) lib;

  shakefile = pkgs.callPackage ./support/nix/build-shake.nix { };

  our-texlive = pkgs.texlive.combine {
    inherit (pkgs.texlive)
      collection-basic
      collection-latex
      xcolor
      preview
      pgf tikz-cd braids pgfplots
      stmaryrd mathpazo
      varwidth xkeyval standalone;
  };

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

  nodeModules = pkgs.importNpmLock.buildNodeModules {
    npmRoot = ./.;
    inherit (pkgs) nodejs;

    derivationArgs = let
      forbiddenRefs = [
        pkgs.python3
      ];
    in {
      nativeBuildInputs = [ pkgs.removeReferencesTo ];
      postInstall = ''
        find "$out" -exec remove-references-to ${lib.concatMapStringsSep " " (x: "-t ${lib.escapeShellArg x}") forbiddenRefs} '{}' +
      '';
      disallowedRequisites = forbiddenRefs;
    };
  };

  setupNodePath = pkgs.makeSetupHook {
    name = "setup-node-path";
  } (pkgs.writeScript "setup-node-path.sh" ''
    addToSearchPath NODE_PATH ${nodeModules}/node_modules
  '');

  # Dependencies for building the 1Lab itself, excluding the shakefile.
  # These are also included in the shell for the shakefile itself so
  # that `cabal run 1lab-shake` works as expected.
  deps = with pkgs; [
    # For building the text and maths:
    gitMinimal dart-sass nodejs setupNodePath

    # For building diagrams:
    poppler-utils our-texlive
  ] ++ lib.optionals interactive [
    (lib.getBin labHaskellPackages.Agda)
    sort-imports
  ];
in
  pkgs.stdenv.mkDerivation rec {
    name = "1lab";

    src = if inNixShell then null else
      with pkgs.nix-gitignore; gitignoreFilterSourcePure (_: _: true) [
        # Keep .git around for extracting page authors
        (compileRecursiveGitignore ./.)
        ".github"
      ] ./.;

    nativeBuildInputs = deps ++ [
      shakefile
    ];

    shellHook = ''
      export out=_build/site
    '';

    LANG = "C.UTF-8";
    buildPhase = ''
      1lab-shake all -j --git-only
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
      inherit deps sort-imports nodeModules;
      texlive = our-texlive;

      shakefile = if !inNixShell then shakefile else
        # A shell for working on the shakefile.
        (shakefile.envFunc { withHoogle = false; }).overrideAttrs (old: {
          nativeBuildInputs = old.nativeBuildInputs ++ deps ++ [
            pkgs.cabal-install
            pkgs.labHaskellPackages.haskell-language-server
          ];
        });
    };
  }
