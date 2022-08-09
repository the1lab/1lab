with import ./nixpkgs.nix;
haskellPackages.override {
  overrides = self: super: {
    Agda = (self.callCabal2nix "Agda" (pkgs.fetchFromGitHub {
      owner = "agda";
      repo = "agda";
      rev = "a52fc3ca191b58e552626988b663bf76c6e8cc42";
      sha256 = "sha256-pkaefBrZDr/1cP7G+uoCtyPDFprFCA6sixJdFNIvuqw=";
    }) {}).overrideAttrs (old: { doCheck = false; });

    vector-hashtables = haskell.lib.dontCheck super.vector-hashtables;
  };
}
