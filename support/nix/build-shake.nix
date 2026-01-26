{ pkgs
, lib
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
, importNpmLock
}:
let
  nodeModules = importNpmLock.buildNodeModules {
    npmRoot = ../..;
    inherit (pkgs) nodejs;

    # To cut down on the image size we maim some references here.
    derivationArgs = let
      forbiddenRefs = [
        pkgs.python3
        pkgs.bashNonInteractive
      ];
    in {
      nativeBuildInputs = [ removeReferencesTo ];
      postInstall = ''
        find "$out" -exec remove-references-to ${lib.concatMapStringsSep " " (x: "-t ${lib.escapeShellArg x}") forbiddenRefs} '{}' +
      '';
      disallowedReferences = forbiddenRefs;
    };
  };
in
stdenv.mkDerivation {
  inherit name;
  src = nix-gitignore.gitignoreSource [] ../shake;
  nativeBuildInputs = [ our-ghc makeWrapper removeReferencesTo ];
  propagatedBuildInputs = [ lua5_3 gmp ];

  buildPhase = ''
  ghc -o ${main} app/${main} -threaded -with-rtsopts "-A128M -N -I0" -rtsopts -iapp -O2 -split-sections \
    -DNODE_BIN_PATH="\"${nodeModules}/node_modules/.bin\"" # see Utils.hs
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
    --prefix NODE_PATH : ${nodeModules}/node_modules
  '';

  disallowedReferences = with labHaskellPackages; [
    shake directory tagsoup
    text containers uri-encode
    process aeson Agda pandoc SHA pandoc-types HTTP
    js-flot js-jquery js-dgtable
  ];
}
