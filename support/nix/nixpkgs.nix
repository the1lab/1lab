args: import (builtins.fetchTarball {
  name   = "1lab-nixpkgs";
  url    = "https://github.com/nixos/nixpkgs/archive/6cfbf89825dae72c64188bb218fd4ceca1b6a9e3.tar.gz";
  sha256 = "sha256:17m78fn3y2x44zgdm428k3l6xamyw6vnz2vd68nj5kxlkbfqnynr";
}) ({
  overlays = [ (import ./haskell-packages.nix) ];
} // args)
