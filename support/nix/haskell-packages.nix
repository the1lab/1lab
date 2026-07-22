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
    rev             = "f4a69107450c2865baa926f7c6ed99894c6333c4";
    sha256          = "sha256-UicvXe/3vV2RlZXjcM7rKA4wIl1AwZUWHYqiXfdG/To=";
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
