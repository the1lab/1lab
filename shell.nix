{ system ? builtins.currentSystem
}:
let
  the1lab = import ./. { inherit system; };
  inherit (the1lab) pkgs shakefile deps sort-imports;
  inherit (pkgs) lib;
in
# Note that mkShell destroys the installPhase.
the1lab.overrideAttrs (old: {
  src = null; # Don't copy anything to the store.

  nativeBuildInputs = old.nativeBuildInputs or [] ++ [
    (lib.getBin pkgs.labHaskellPackages.Agda)
    sort-imports
  ];

  passthru = old.passthru // {
    shakefile =
      (shakefile.envFunc { withHoogle = false; }).overrideAttrs (old: {
        nativeBuildInputs = old.nativeBuildInputs ++ deps ++ [
          pkgs.cabal-install
          pkgs.labHaskellPackages.haskell-language-server
          sort-imports
        ];
      });
  };
})
