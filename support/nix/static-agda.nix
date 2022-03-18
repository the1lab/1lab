with import ./nixpkgs.nix;
let haskellPackages = import ./haskell-packages.nix; in
stdenv.mkDerivation {
  name = "agda-static";
  src = fetchFromGitHub {
    owner = "agda";
    repo = "agda";
    rev = "v${haskellPackages.Agda.version}";
    sha256 = "0p6jh8hyyf7xg0sni2rchck2fd1wyr5v106dfxxm09krxxawh0nh";
  };

  nativeBuildInputs = [
    (haskellPackages.ghcWithPackages (pkgs: with pkgs;
      [ cabal-install aeson async blaze-html boxes
        case-insensitive data-hash edit-distance
        equivalence gitrev hashtables
        monad-control murmur-hash parallel
        regex-tdfa split strict unordered-containers
        uri-encode zlib alex happy ]))
  ];

  buildInputs = [
    glibc
    glibc.static
    pkgsStatic.gmp
    pkgsStatic.libffi
    pkgsStatic.ncurses
    zlib.static
  ];

  # Since we have static glibc, etc. we have to build
  # the Agda Cabal setup with static libraries as well
  configurePhase = ''
  ghc -static -optl-static -optl-pthread Setup.hs
  
  ./Setup configure \
    --prefix=$out \
    --bindir=$out/bin \
    --libdir=$out/lib \
    --datadir=$out/share \
    --enable-executable-static \
    --disable-executable-dynamic \
    --disable-shared \
    --enable-executable-stripping \
    --ghc-option=-j
  '';

  buildPhase = ''
  ./Setup build
  '';

  # This is the correct invocation to install Agda using
  # Cabal, not "./Setup install" as one would expect
  installPhase = ''
  ./Setup copy
  rm -rfv $out/lib # delete Haskell libraries
  '';
}