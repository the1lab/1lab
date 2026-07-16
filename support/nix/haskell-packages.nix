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
    rev             = "208ac8ca35ddfd971412438da6fcb29aa54e9b4b";
    sha256          = "sha256-uFhZiTYpLYBtCOfrO18mRbXNFazegFjk/L8gBOzXwZs=";
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
