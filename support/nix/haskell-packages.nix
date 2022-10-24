pkgs: super:
let
  thunkSource = (import ./dep/nix-thunk { inherit pkgs; }).thunkSource;
in
  {
    haskell = super.haskell // {
      packageOverrides = self: super: {
        Agda = pkgs.haskell.lib.overrideCabal
          (self.callCabal2nixWithOptions "Agda" (thunkSource ./dep/Agda) "-f optimise-heavily" {})
          {
            doCheck = false;
            doHaddock = false;
            enableExecutableProfiling = false;
            enableLibraryProfiling = false;
          };
      };
    };
  }
