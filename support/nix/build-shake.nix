{ our-ghc
, removeReferencesTo
, haskellPackages
, stdenv
, upx
, lua5_3
, name
, gmp
, main
}:
stdenv.mkDerivation {
  inherit name;
  src = ../shake;
  nativeBuildInputs = [ our-ghc removeReferencesTo upx ];
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
  '';

  disallowedReferences = with haskellPackages; [
    shake directory tagsoup
    text containers uri-encode
    process aeson Agda pandoc SHA pandoc-types HTTP
    js-flot js-jquery js-dgtable
  ];
}
