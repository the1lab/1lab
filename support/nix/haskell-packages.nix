with import ./nixpkgs.nix;
haskellPackages.override {
  overrides = self: super: {
    Agda = (self.callCabal2nix "Agda" (pkgs.fetchFromGitHub {
      owner = "agda";
      repo = "agda";
      rev = "5d2d77abbc0c97f5b23d7089797c3ef8796508dc";
      sha256 = "sha256-Bo0vJ+en2ajs4RLJk0EQ4rDFFR/xlZvQxz5TdRrL16s=";
    }) {}).overrideAttrs (old: { doCheck = false; });

    vector-hashtables = haskell.lib.dontCheck super.vector-hashtables;
  };
}
