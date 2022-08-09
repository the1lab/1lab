{ pkgs
, our-ghc
, makeWrapper
, removeReferencesTo
, haskellPackages
, stdenv
, upx
, lua5_3
, name
, gmp
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
  src = ../shake;
  nativeBuildInputs = [ our-ghc makeWrapper removeReferencesTo upx ];
  propagatedBuildInputs = [ lua5_3 gmp ];

  buildPhase = ''
  ghc -o ${main} app/${main} -threaded -rtsopts -iapp -O2 -split-sections
  '';

  installPhase = ''
  mkdir -p $out/bin
  strip ${main}
  upx ${main}
  cp ${main} $out/bin/${name}
  remove-references-to -t ${haskellPackages.pandoc-types} $out/bin/${name}
  remove-references-to -t ${haskellPackages.pandoc}       $out/bin/${name}
  remove-references-to -t ${haskellPackages.Agda}         $out/bin/${name}
  remove-references-to -t ${haskellPackages.shake}        $out/bin/${name}
  remove-references-to -t ${haskellPackages.HTTP}         $out/bin/${name}
  remove-references-to -t ${haskellPackages.js-flot}      $out/bin/${name}
  remove-references-to -t ${haskellPackages.js-jquery}    $out/bin/${name}
  remove-references-to -t ${haskellPackages.js-dgtable}   $out/bin/${name}
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
