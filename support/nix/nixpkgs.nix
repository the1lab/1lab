{ system ? builtins.currentSystem
, ...
}@args: import (builtins.fetchTarball {
  name   = "1lab-nixpkgs";
  url    = "https://github.com/nixos/nixpkgs/archive/e99366c665bdd53b7b500ccdc5226675cfc51f45.tar.gz";
  sha256 = "sha256-EiED5k6gXTWoAIS8yQqi5mAX6ojnzpHwAQTS3ykeYMg=";
}) ({
  overlays = [ (import ./haskell-packages.nix) ];
} // args)
