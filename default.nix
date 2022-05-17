with builtins;
with import ./support/nix/nixpkgs.nix;
let
  haskellPackages = import ./support/nix/haskell-packages.nix;
  our-ghc = haskellPackages.ghcWithPackages (pkgs: with pkgs; [
    shake directory tagsoup
    text containers uri-encode
    process aeson Agda pandoc SHA
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

  make-font = { type, family, hash, prefix ? "$out" }:
    let
      p = fetchurl {
        url = "https://cubical.1lab.dev/static/${type}/${family}.${type}";
        sha256 = hash;
      };
    in ''
      mkdir -p ${prefix}/static/${type};
      install -Dm 644 ${p} ${prefix}/static/${type}/${family}.${type};
    '';

  fonts = { prefix ? "$out" }: concatStringsSep "\n" (map make-font [
    {
      type = "woff2";
      family = "iosevk-abbie-regular";
      hash = "1zpn3qam0xywvmzz5mjjh23asx9ysnp6ali1agr770qimlxi5zmc";
      inherit prefix;
    }
    {
      type = "ttf";
      family = "iosevk-abbie-regular";
      hash = "0x9nbpm3jf18wlpd7ysbgzl31lwr6qiip5496ma8l72pn812k39g";
      inherit prefix;
    }
  ]);

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
      our-ghc shakefile static-agda

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

    # Copy bits of Iosevka
    ${fonts {}}
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
