{ pkgs
, nix-gitignore
, our-ghc
, makeWrapper
, removeReferencesTo
, haskellPackages
, stdenv
, upx
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
  nativeBuildInputs = [ our-ghc makeWrapper removeReferencesTo upx ];
  propagatedBuildInputs = [ lua5_3 gmp ];

  buildPhase = ''
  ghc -o ${main} app/${main} -threaded -rtsopts -iapp -O2 -split-sections
  '';

  installPhase = ''
  mkdir -p $out/bin
  strip ${main}
  remove-references-to -t ${haskellPackages.pandoc-types} ${main}
  remove-references-to -t ${haskellPackages.pandoc}       ${main}
  remove-references-to -t ${haskellPackages.Agda}         ${main}
  remove-references-to -t ${haskellPackages.shake}        ${main}
  remove-references-to -t ${haskellPackages.HTTP}         ${main}
  remove-references-to -t ${haskellPackages.js-flot}      ${main}
  remove-references-to -t ${haskellPackages.js-jquery}    ${main}
  remove-references-to -t ${haskellPackages.js-dgtable}   ${main}
  upx ${main}
  cp ${main} $out/bin/${name}
  wrapProgram $out/bin/${name} \
    --prefix PATH : ${nodeDependencies}/bin \
    --prefix NODE_PATH : ${nodeDependencies}/lib/node_modules
  '';

  disallowedReferences = with haskellPackages; [
    shake directory tagsoup
    text containers uri-encode
    process aeson Agda pandoc SHA pandoc-types HTTP
    js-flot js-jquery js-dgtable
  ];
}
