args: import (builtins.fetchTarball {
  name   = "1lab-nixpkgs";
  url    = "https://github.com/nixos/nixpkgs/archive/45f4a9dfc86f0628270e35fb3bcdec035d6205df.tar.gz";
  sha256 = "sha256:1z6ssk35am53pgf5h907302mx47kvgqnp4qm2z3xfy3vyly19xn8";
}) ({
  overlays = [ (import ./haskell-packages.nix) ];
} // args)
