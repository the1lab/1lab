with import <nixpkgs> {};
with haskell.lib;
let
  static-agda =
    stdenv.mkDerivation {
      name = "agda-static";
      src = fetchFromGitHub {
        owner = "agda";
        repo = "agda";
        rev = "v2.6.2.1";
        sha256 = "0p6jh8hyyf7xg0sni2rchck2fd1wyr5v106dfxxm09krxxawh0nh";
      };

      nativeBuildInputs = [
        (haskellPackages.ghcWithPackages (pkgs: with pkgs;
          [ cabal-install aeson async blaze-html boxes
            case-insensitive data-hash edit-distance
            equivalence gitrev hashtables
            monad-control murmur-hash parallel
            regex-tdfa split strict unordered-containers
            uri-encode zlib alex happy ]))
      ];

      buildInputs = [
        glibc
        glibc.static
        (gmp.override { withStatic = true; }).static
        (libffi.overrideAttrs (old: { dontDisableStatic = true; }))
        zlib.static
        (ncurses.override { enableStatic = true; })
      ];

      # Since we have static glibc, etc. we have to build
      # the Agda Cabal setup with static libraries as well
      configurePhase = ''
      ghc -static -optl-static -optl-pthread Setup.hs
      
      ./Setup configure \
        --prefix=$out \
        --bindir=$out/bin \
        --libdir=$out/lib \
        --datadir=$out/share \
        --enable-executable-static \
        --disable-executable-dynamic \
        --disable-shared \
        --enable-executable-stripping \
        --ghc-option=-j
      '';

      buildPhase = ''
      ./Setup build
      '';

      # This is the correct invocation to install Agda using
      # Cabal, not "./Setup install" as one would expect
      installPhase = ''
      ./Setup copy
      rm -rfv $out/lib # delete Haskell libraries
      '';
    };

  the-lab = import ./default.nix;
  build-env = the-lab.deps;

  texlive-layer = dockerTools.buildImage {
    name = "pltamy/1lab-texlive";
    tag = "latest";
    contents = [ the-lab.texlive ];
  };
in
  dockerTools.streamLayeredImage {
    name = "pltamy/1lab";
    tag = "latest";
    fromImage = texlive-layer;

    maxLayers = 10;

    contents = the-lab.deps ++ [ 
      pkgs.pkgsStatic.busybox # Need a shell, so go with static busybox
      static-agda

      # Needed for Github Actions:
      rsync
    ];

    config = {
      WorkingDir = "/workspace";
      Env = [
        "LANG=C.UTF-8" # Needed for GHC to set the correct encoding on handles
        "PATH=/lib/node_modules/.bin/:/bin/"
        
        # Needed for Github Actions:
        "LD_LIBRARY_PATH=${lib.makeLibraryPath [ pkgs.stdenv.cc.cc ]}"
        "GIT_SSL_CAINFO=${cacert}/etc/ssl/certs/ca-bundle.crt"
        "SSL_CERT_FILE=${cacert}/etc/ssl/certs/ca-bundle.crt"
      ];
    };

    fakeRootCommands = ''
    mkdir -p ./tmp ./lib64 ./usr/bin ./root/static ./etc
    echo "ID=nixos" > ./etc/os-release
    cp ./bin/env ./usr/bin/

    ${the-lab.fonts { prefix = "./root/"; }}

    mkdir -p ./root/static/otf
    cp ${gyre-fonts}/share/fonts/truetype/texgyrepagella*.otf ./root/static/otf -rv

    # Needed for Github Actions
    ln -s ${pkgs.glibc}/lib/ld-linux-x86-64.so.2 ./lib64/ld-linux-x86-64.so.2
    '';
  }