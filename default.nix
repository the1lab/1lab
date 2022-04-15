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

  shakefile = stdenv.mkDerivation {
    name = "1lab-shake";
    src = filterSource (path: type: match ".*Shakefile.*" path != null) ./.;
    nativeBuildInputs = [ our-ghc removeReferencesTo ];
    buildInputs = [];

    buildPhase = ''
    ghc Shakefile.hs -threaded -rtsopts
    '';

    installPhase = ''
    mkdir -p $out/bin
    cp Shakefile $out/bin/1lab-shake
    remove-references-to -t ${haskellPackages.pandoc-types} $out/bin/1lab-shake
    remove-references-to -t ${haskellPackages.pandoc}       $out/bin/1lab-shake
    remove-references-to -t ${haskellPackages.Agda}         $out/bin/1lab-shake
    remove-references-to -t ${haskellPackages.shake}        $out/bin/1lab-shake
    remove-references-to -t ${haskellPackages.HTTP}         $out/bin/1lab-shake
    remove-references-to -t ${haskellPackages.js-flot}      $out/bin/1lab-shake
    remove-references-to -t ${haskellPackages.js-jquery}    $out/bin/1lab-shake
    remove-references-to -t ${haskellPackages.js-dgtable}   $out/bin/1lab-shake
    '';

    disallowedReferences = with haskellPackages; [
      shake directory tagsoup
      text containers uri-encode
      process aeson Agda pandoc SHA pandoc-types HTTP
      js-flot js-jquery js-dgtable
    ];
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
      git sassc nodePackages.katex
      haskellPackages.agda-reference-filter
      haskellPackages.agda-fold-equations

      # For building diagrams:
      poppler_utils rubber our-texlive
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
        git sassc pandoc nodePackages.katex
        haskellPackages.agda-reference-filter
        haskellPackages.agda-fold-equations
        python

        # For building diagrams:
        poppler_utils rubber
      ];

      texlive = our-texlive;
      ghc = our-ghc;
      fonts = fonts;
    };
  }
