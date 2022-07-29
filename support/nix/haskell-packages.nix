with import ./nixpkgs.nix;
haskellPackages.override {
  overrides = self: super: {
    Agda = (self.callCabal2nix "Agda" (pkgs.fetchFromGitHub {
      owner = "agda";
      repo = "agda";
      rev = "4dfda5b1ed0f6e3ae1f9d7d056ecab63a6c39c0a";
      sha256 = sha256:8JtYyRf5wdhFvXzYclZnnELuKVv1y8mh8QBW3QlIhC0=;
    }) {}).overrideAttrs (old: { doCheck = false; });

    vector-hashtables = haskell.lib.dontCheck super.vector-hashtables;
  };
}
