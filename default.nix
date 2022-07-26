with builtins;
with import ./support/nix/nixpkgs.nix;
let
  haskellPackages = import ./support/nix/haskell-packages.nix;
  our-ghc = haskellPackages.ghcWithPackages (pkgs: with pkgs; [
    shake directory tagsoup
    text containers uri-encode
    process aeson Agda pandoc SHA
    fsnotify
  ]);

  static-agda = import ./support/nix/static-agda.nix;

  our-texlive = texlive.combine {
    inherit (texlive)
      collection-basic
      collection-latex
      xcolor
      preview
      pgf tikz-cd
      mathpazo
      varwidth xkeyval standalone;
  };

  shakefile = import ./support/nix/build-shake.nix
    {
      inherit our-ghc haskellPackages;
      inherit (pkgs) removeReferencesTo stdenv upx lua5_3 gmp;
      name = "1lab-shake";
      main = "Main.hs";
    };
in
  stdenv.mkDerivation rec {
    name = "cubical-1lab";
    src =
      filterSource
        (path: type:
          match ".+\\.agdai$" path == null &&
          match "^_build/.*$" path == null)
        ./.;

    buildInputs = [
      # For driving the compilation:
      our-ghc shakefile

      # For building the text and maths:
      gitMinimal sassc

      # For building diagrams:
      poppler_utils our-texlive
    ];

    buildPhase = ''
    export LANG=C.UTF-8;
    1lab-shake all -j
    '';

    installPhase = ''
    mkdir -p $out{,/css/,/lib/};

    # Copy our build artifacts
    cp -Lrv _build/html/* $out;

    # Copy KaTeX CSS and fonts
    cp -Lrv --no-preserve=mode ${nodePackages.katex}/lib/node_modules/katex/dist/{katex.min.css,fonts} $out/css/;
    mkdir -p $out/static/ttf/
    cp -Lrv --no-preserve=mode ${pkgs.julia-mono}/share/fonts/truetype/JuliaMono-Regular.ttf $out/static/ttf/julia-mono.ttf
    '';

    passthru = {
      deps = [
        shakefile

        # For building the text and maths:
        gitMinimal sassc

        # For building diagrams:
        poppler_utils
      ];

      texlive = our-texlive;
      ghc = our-ghc;
      inherit fonts shakefile;
      agda-typed-html = import ./support/nix/build-shake.nix
        {
          inherit our-ghc haskellPackages;
          inherit (pkgs) removeReferencesTo stdenv upx lua5_3 gmp;
          main = "Wrapper.hs";
          name = "agda-typed-html";
        };
    };
  }
