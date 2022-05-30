with import ./nixpkgs.nix;
haskellPackages.override {
  overrides = self: super: {
    Agda =
      haskell.lib.disableLibraryProfiling (haskell.lib.overrideCabal super.Agda {
        version = "2.6.2.2";
        sha256 = sha256:5b43YXF7FE9k52DYWJ7G/cDdpg1AElxJzdSPVBhcUno=;
      });
  };
}
