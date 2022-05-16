with import ./nixpkgs.nix;
haskellPackages.override {
  overrides = self: super: {
    Agda =
      haskell.lib.appendConfigureFlag
        (haskell.lib.disableLibraryProfiling (haskell.lib.overrideCabal super.Agda {
          version = "2.6.2.1";
          sha256 = sha256:03dw7jfqr3ffik6avigm525djqh2gn5c3qwnb2h6298zkr9lch9w;
        }))
        "--enable-split-sections";
  };
}
