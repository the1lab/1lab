with import ./support/nix/nixpkgs.nix;
with haskell.lib;
let
  the-lab = import ./default.nix;
  haskellPackages = import ./support/nix/haskell-packages.nix;

  nodeEnv = import ./support/nix/node/node-env.nix {
    inherit (pkgs) stdenv lib python2 runCommand writeTextFile writeShellScript;
    inherit pkgs nodejs;
    libtool = if pkgs.stdenv.isDarwin then pkgs.darwin.cctools else null;
  };

  # To cut down on the image size we maim all references to nodejs,
  # Python and bash here. The result is basically a big blob of data.
  deps = (import ./support/nix/node/node-dependencies.nix {
    inherit (pkgs) fetchurl nix-gitignore stdenv lib fetchgit;
    inherit nodeEnv;
  }).nodeDependencies.overrideDerivation (old: {
    installPhase = ''
    ${old.installPhase}
    find $out -print0 | xargs -0 ${pkgs.removeReferencesTo}/bin/remove-references-to -t ${pkgs.nodejs}
    find $out -print0 | xargs -0 ${pkgs.removeReferencesTo}/bin/remove-references-to -t ${pkgs.python3}
    find $out -print0 | xargs -0 ${pkgs.removeReferencesTo}/bin/remove-references-to -t ${pkgs.bash}
    '';
  });
in
  dockerTools.streamLayeredImage {
    name = "pltamy/1lab";
    tag = "latest";

    contents = the-lab.deps ++ [
      pkgs.pkgsStatic.busybox # Need a shell, so go with static busybox
      pkgs.nodejs-slim-14_x
      the-lab.texlive

      # Need to include Agda data files for the primitive modules:
      haskellPackages.Agda.data
      haskellPackages.pandoc.data

      # Needed for Github Actions:
      gnutar
      rsync
      deps
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

        "NODE_DEPS_PATH=${deps}/lib/node_modules"
      ];
    };

    fakeRootCommands = ''
    mkdir -p ./tmp ./lib64 ./usr/bin ./root/static ./etc
    echo "ID=nixos" > ./etc/os-release
    cp ./bin/env ./usr/bin/

    ${the-lab.fonts { prefix = "./root/"; }}

    # Needed for Github Actions
    ln -s ${pkgs.glibc}/lib/ld-linux-x86-64.so.2 ./lib64/ld-linux-x86-64.so.2
    ln -sf ${pkgs.gnutar}/bin/tar ./bin/tar
    '';
  }
