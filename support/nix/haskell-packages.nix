with import ./nixpkgs.nix;
haskellPackages.override {
  overrides = self: super: {
    Agda = (haskellPackages.callCabal2nix "Agda" (pkgs.fetchFromGitHub {
      owner = "agda";
      repo = "agda";
      rev = "d36cfd1fbf88c49d2169fa5fafc762d64c985a72";
      sha256 = sha256:0bkw3gh58kpixr0f7h60b0x3yzhinxbnzv9jmrzrdrivb9jvf7si;
    }) {}).overrideAttrs (old: { doCheck = false; });
  };
}
