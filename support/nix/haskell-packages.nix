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
    labHaskellPackages = super.haskell.packages.ghc984.override (old: {
      overrides = hself: hsuper: {
        infinite-list = hsuper.callHackageDirect {
          pkg    = "infinite-list";
          ver    = "0.1.2";
          sha256 = "sha256-OUNCBVKCHFPjtJK/Lm4PG6ldKvqSySA0TwnaY9estzo=";
        } {};

        vector-hashtables = hsuper.callHackageDirect {
          pkg    = "vector-hashtables";
          ver    = "0.1.2.1";
          sha256 = "sha256-YLGkB9mm6jYFlqNv7oUNO0CeXDZNIdWJOFtczmSXN+s=";
        } {};

        zstd = hsuper.callHackageDirect {
          pkg    = "zstd";
          ver    = "0.1.3.0";
          sha256 = "sha256-2H+goIZ/JpXkIJ8K821x2dAhd7I+fVoOfx7a7B4IMD0=";
        } {};

        hs-speedscope = hsuper.callHackageDirect {
          pkg    = "hs-speedscope";
          ver    = "0.3.0";
          sha256 = "sha256-ZaaTMV3HKmJU+i9QELMqnhOb3eSY5ROPSgofbe4QCvs=";
        } {};

        Agda = noJunk (hsuper.callCabal2nixWithOptions "Agda" (thunkSource ./dep/Agda) "-f optimise-heavily -f debug" {});
      };
    });
  }
