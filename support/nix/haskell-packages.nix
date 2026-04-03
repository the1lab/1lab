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

  agda = hsuper: suf: flags: noJunk (
    hsuper.callCabal2nixWithOptions "Agda-${suf}" (thunkSource ./dep/Agda) flags {}
  );
in
  {
    labHaskellPackages = super.haskell.packages.ghc910.override (old: {
      overrides = hself: hsuper: {
        Agda = (agda hsuper "debug" "-foptimise-heavily -fdebug").overrideAttrs (old: {
          passthru = old.passthru // {
            nodebug = noProfile (agda hsuper "nodebug" "-foptimise-heavily");
          };
        });
      };
    });
  }
