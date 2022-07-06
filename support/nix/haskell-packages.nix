with import ./nixpkgs.nix;
haskellPackages.override {
  overrides = self: super: {
    Agda = (self.callCabal2nix "Agda" (pkgs.fetchFromGitHub {
      owner = "agda";
      repo = "agda";
      rev = "41b2f45dbe83acda7e28d4e150ca8548f04b92fb";
      sha256 = "sha256-jBvyp5jlwNAEtwe+n7kJp3cRib+n7r1vsBlTlJolhRs=";
    }) {}).overrideAttrs (old: { doCheck = false; });

    vector-hashtables = haskell.lib.dontCheck super.vector-hashtables;
  };
}
