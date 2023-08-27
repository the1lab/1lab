args: import (builtins.fetchTarball {
  name   = "1lab-nixpkgs";
  url    = "https://github.com/nixos/nixpkgs/archive/cc4bb87f5457ba06af9ae57ee4328a49ce674b1b.tar.gz";
  sha256 = "sha256:072q50x5p06qjf0cvz68gcrbkpv94bdl55h71j0rz6bgfhaqmiwy";
}) ({
  overlays = [ (import ./haskell-packages.nix) ];
} // args)
