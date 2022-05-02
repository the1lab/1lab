{ our-ghc, removeReferencesTo, haskellPackages, stdenv
, name
, main
}:
stdenv.mkDerivation {
  inherit name;
  src = ../shake;
  nativeBuildInputs = [ our-ghc removeReferencesTo ];
  buildInputs = [];

  buildPhase = ''
  ghc -o ${main} app/${main} -threaded -rtsopts -iapp -O2
  '';

  installPhase = ''
  mkdir -p $out/bin
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
