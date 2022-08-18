import (builtins.fetchTarball {
  name = "1lab-nixpkgs";
  url = "https://github.com/nixos/nixpkgs/archive/6c6409e965a6c883677be7b9d87a95fab6c3472e.tar.gz";
  sha256 = "sha256:0l1py0rs1940wx76gpg66wn1kgq2rv2m9hzrhq5isz42hdpf4q6r";
}) {
  overlays = [ (import ./haskell-packages.nix) ];
}
