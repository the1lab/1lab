args: import (builtins.fetchTarball {
  name   = "1lab-nixpkgs";
  url    = "https://github.com/nixos/nixpkgs/archive/bf39054f8666a98196671269351e42db7e0db6bc.tar.gz";
  sha256 = "sha256:0f9k3c6qjsn2aw5jhyz8pqs5saajgi4wkrbj0yrsp1k0vpx4yqx6";
}) ({
  overlays = [ (import ./haskell-packages.nix) ];
} // args)
