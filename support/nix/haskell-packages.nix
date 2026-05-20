pkgs: super:
let
  inherit (pkgs) lib;
  hlib = pkgs.haskell.lib.compose;

  noJunk = hlib.overrideCabal {
    doCheck = false;
    doHaddock = false;
    testHaskellDepends = [];
  };

  noProfile = hlib.overrideCabal {
    enableExecutableProfiling = false;
    enableLibraryProfiling = false;
  };

  src = pkgs.fetchgit {
    url             = "https://codeberg.org/1lab/mikan.git";
    rev             = "b168a06b76cd4fce733b102a40397a784e23a2fc";
    sha256          = "sha256-dfH159gbxUeiKJMAZ3WVUDrPChFpu/A8hMmNqzCHy34=";
    fetchSubmodules = false;
  };

  mikan = hsuper: suf: flags: noJunk (
    hsuper.callCabal2nixWithOptions "Mikan-${suf}" src flags {}
  );
in
  {
    labHaskellPackages = super.haskell.packages.ghc910.override (old: {
      overrides = hself: hsuper: {
        Mikan = (mikan hsuper "debug" "-foptimise-heavily -fdebug").overrideAttrs (old: {
          passthru = old.passthru // {
            nodebug = noProfile (mikan hsuper "nodebug" "-foptimise-heavily");
          };
        });
      };
    });
  }
