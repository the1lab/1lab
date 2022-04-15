with import ./support/nix/nixpkgs.nix;
with haskell.lib;
let
  static-agda = import ./support/nix/static-agda.nix;
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

    # Needed for Github Actions
    ln -s ${pkgs.glibc}/lib/ld-linux-x86-64.so.2 ./lib64/ld-linux-x86-64.so.2
    '';
  }
