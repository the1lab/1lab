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
    rev             = "a2b0cfeb0babc37f573ac78be6449d5ce6a47fdc";
    sha256          = "sha256-8HtElGCKpPUO55kOsiD5G/JWy3+NU1Z/TF26szrwORA=";
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
