pkgs: super:
let
  thunkSource = (import ./dep/nix-thunk { inherit pkgs; }).thunkSource;
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
in
  {
    labHaskellPackages = super.haskell.packages.ghc910.override (old: {
      overrides = hself: hsuper: {
        Agda = noJunk (hsuper.callCabal2nixWithOptions "Agda" (thunkSource ./dep/Agda) "-f optimise-heavily -f debug" {});
      };
    });
  }
