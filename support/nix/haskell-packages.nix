pkgs: super:
let
  thunkSource = (import ./dep/nix-thunk { inherit pkgs; }).thunkSource;
  noJunk = x: pkgs.haskell.lib.overrideCabal x {
    doCheck = false;
    doHaddock = false;
    testHaskellDepends = [];
  };
  noProfile = x: pkgs.haskell.lib.overrideCabal x {
    enableExecutableProfiling = false;
    enableLibraryProfiling = false;
  };
in
  {
    # Can't just override all Haskell packages because callCabal2nix
    # somehow depends on mime-types
    labHaskellPackages = super.haskell.packages.ghc946.override (old: {
      overrides = self: super: {
        infinite-list = super.callHackageDirect {
          pkg    = "infinite-list";
          ver    = "0.1.2";
          sha256 = "sha256-OUNCBVKCHFPjtJK/Lm4PG6ldKvqSySA0TwnaY9estzo=";
        } {};

        Agda = noJunk (super.callCabal2nixWithOptions "Agda" (thunkSource ./dep/Agda) "-f optimise-heavily -f debug" {});
      };
    });
  }
