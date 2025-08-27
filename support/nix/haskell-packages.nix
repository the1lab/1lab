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
    labHaskellPackages = super.haskell.packages.ghc984.override (old: {
      overrides = self: super: {
        infinite-list = super.callHackageDirect {
          pkg    = "infinite-list";
          ver    = "0.1.2";
          sha256 = "sha256-OUNCBVKCHFPjtJK/Lm4PG6ldKvqSySA0TwnaY9estzo=";
        } {};

        vector-hashtables = super.callHackageDirect {
          pkg    = "vector-hashtables";
          ver    = "0.1.2.1";
          sha256 = "sha256-YLGkB9mm6jYFlqNv7oUNO0CeXDZNIdWJOFtczmSXN+s=";
        } {};

        zstd = super.callHackageDirect {
          pkg    = "zstd";
          ver    = "0.1.3.0";
          sha256 = "sha256-2H+goIZ/JpXkIJ8K821x2dAhd7I+fVoOfx7a7B4IMD0=";
        } {};

        hs-speedscope = super.callHackageDirect {
          pkg    = "hs-speedscope";
          ver    = "0.3.0";
          sha256 = "sha256-ZaaTMV3HKmJU+i9QELMqnhOb3eSY5ROPSgofbe4QCvs=";
        } {};

        Agda = noJunk (super.callCabal2nixWithOptions "Agda" (thunkSource ./dep/Agda) "-f optimise-heavily -f debug" {});
      };
    });
  }
