{ pkgs
, nix-gitignore
, our-ghc
, makeWrapper
, removeReferencesTo
, labHaskellPackages
, stdenv
, lua5_3
, gmp
, name
, main
}:
let
  nodeEnv = import ./node/node-env.nix {
    inherit (pkgs) stdenv lib python2 runCommand writeTextFile writeShellScript nodejs;
    inherit pkgs;
    libtool = if pkgs.stdenv.isDarwin then pkgs.darwin.cctools else null;
  };

  # To cut down on the image size we maim all references to Python and bash here.
  nodeDependencies = (import ./node/node-dependencies.nix {
    inherit (pkgs) fetchurl nix-gitignore stdenv lib fetchgit;
    inherit nodeEnv;
  }).nodeDependencies.overrideDerivation (old: {
    installPhase = ''
    ${old.installPhase}
    find $out -print0 | xargs -0 ${pkgs.removeReferencesTo}/bin/remove-references-to -t ${pkgs.python3}
    find $out -print0 | xargs -0 ${pkgs.removeReferencesTo}/bin/remove-references-to -t ${pkgs.bash}
    '';
  });
in
stdenv.mkDerivation {
  inherit name;
  src = nix-gitignore.gitignoreSource [] ../shake;
  nativeBuildInputs = [ our-ghc makeWrapper removeReferencesTo ];
  propagatedBuildInputs = [ lua5_3 gmp ];

  buildPhase = ''
  ghc -o ${main} app/${main} -threaded -with-rtsopts -A128M -rtsopts -iapp -O2 -split-sections -DNODE_BIN_PATH="\"${nodeDependencies}/bin\""
  '';

  installPhase = ''
  mkdir -p $out/bin
  strip ${main}
  remove-references-to -t ${labHaskellPackages.pandoc-types} ${main}
  remove-references-to -t ${labHaskellPackages.pandoc}       ${main}
  remove-references-to -t ${labHaskellPackages.Agda}         ${main}
  remove-references-to -t ${labHaskellPackages.shake}        ${main}
  remove-references-to -t ${labHaskellPackages.HTTP}         ${main}
  remove-references-to -t ${labHaskellPackages.js-flot}      ${main}
  remove-references-to -t ${labHaskellPackages.js-jquery}    ${main}
  remove-references-to -t ${labHaskellPackages.js-dgtable}   ${main}
  cp ${main} $out/bin/${name}
  wrapProgram $out/bin/${name} \
    --prefix PATH : ${nodeDependencies}/bin \
    --prefix NODE_PATH : ${nodeDependencies}/lib/node_modules
  '';

  disallowedReferences = with labHaskellPackages; [
    shake directory tagsoup
    text containers uri-encode
    process aeson Agda pandoc SHA pandoc-types HTTP
    js-flot js-jquery js-dgtable
  ];
}
