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
    rev             = "0f415fe6d1e9c5430bba3451ff93c7869041b1d3";
    sha256          = "sha256-+z6zSVTfPWndQsy2zRjl2vmFLcvIGZ4ReDI059fhT+4=";
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
