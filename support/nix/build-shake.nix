{ pkgs
, stdenv
, lib
, nix-gitignore
, removeReferencesTo
, labHaskellPackages
}:
let
  hlib = pkgs.haskell.lib.compose;

  # To cut down on the image size we maim some references.
  forbiddenRefs = with labHaskellPackages; [
    shake tagsoup uri-encode
    aeson pandoc SHA pandoc-types HTTP
    js-flot js-jquery js-dgtable

    Agda.nodebug
  ];

  root = nix-gitignore.gitignoreSource [] ../shake;
in
  lib.pipe (labHaskellPackages.callCabal2nix "1lab-shake" root {
    Agda = labHaskellPackages.Agda.nodebug;
  }) [
    (hlib.addBuildTools [ removeReferencesTo ])
    (hlib.overrideCabal (drv: {
      postInstall = drv.postInstall or "" + ''
        find "$out/bin" -exec remove-references-to ${lib.concatMapStringsSep " " (x: "-t ${lib.escapeShellArg x}") forbiddenRefs} '{}' +
      '';
      # On Darwin the references remain through symbolic links in /lib/links/*.dylib
      disallowedRequisites = lib.optionals (!stdenv.hostPlatform.isDarwin) forbiddenRefs;
    }))
  ]
