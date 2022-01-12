let nixpkgs-version = "release-21.11"; in
with builtins;
with
  import (fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${nixpkgs-version}.tar.gz";
    sha256 = "13im9ag9286bzqpmszg4ya9flvrhl40h6v4gv1g8png1dg0ng1wp";
  }) {};
let
  agda-fold-equations = haskellPackages.callCabal2nix
    "agda-fold-equations"
    (fetchGit {
      url = "https://git.amelia.how/amelia/agda-fold-equations.git";
      rev = "509bc021200b0de7713a0fdb27c730eaff3be206";
    }) {};

  agda-reference-filter = haskellPackages.callCabal2nix
    "agda-fold-equations"
    (fetchGit {
      url = "https://git.amelia.how/amelia/agda-reference-filter.git";
      rev = "082b5576e799fe8aa28e7d09cf415ac6c9e0596b";
    }) {};

  our-ghc = ghc.withPackages (pkgs: with pkgs; [
    shake directory tagsoup
    text containers uri-encode
    process

    agda-fold-equations
    agda-reference-filter
  ]);

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

  make-font = { type, family, hash }:
    let
      p = fetchurl {
        url = "https://cubical.1lab.dev/static/${type}/${family}.${type}";
        sha256 = hash;
      };
    in ''
      mkdir -p $out/static/${type}
      cp ${p} $out/static/${type};
    '';

  fonts = concatStringsSep "\n" (map make-font [
    {
      type = "woff2";
      family = "iosevk-abbie-regular";
      hash = "1zpn3qam0xywvmzz5mjjh23asx9ysnp6ali1agr770qimlxi5zmc";
    }
    {
      type = "ttf";
      family = "iosevk-abbie-regular";
      hash = "0x9nbpm3jf18wlpd7ysbgzl31lwr6qiip5496ma8l72pn812k39g";
    }
  ]);
in
  stdenv.mkDerivation {
    name = "cubical-1lab";
    src =
      filterSource
        (path: type:
          match ".+\\.agdai$" path == null &&
          match "^_build/.*$" path == null)
        ./.;

    buildInputs = [
      # For driving the compilation:
      our-ghc agda 

      # For building the text and maths:
      git sassc pandoc nodePackages.katex

      # For building diagrams:
      poppler_utils rubber our-texlive

      # Static fonts:
      gyre-fonts
    ];

    buildPhase = ''
    export LANG=C.UTF-8
    runghc ./Shakefile.hs all -j
    '';

    installPhase = ''
    mkdir -p $out{,/css/}

    # Copy our build artifacts
    cp -rv _build/html/* $out

    # Copy KaTeX CSS and fonts
    cp ${nodePackages.katex}/lib/node_modules/katex/dist/{katex.min.css,fonts} $out/css/ -rv

    # Copy bits of Iosevka
    ${fonts}

    mkdir -p $out/static/otf
    cp ${gyre-fonts}/share/fonts/truetype/texgyrepagella*.otf $out/static/otf -rv
    '';
  }