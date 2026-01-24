{ pkgs
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
    aeson Agda pandoc SHA pandoc-types HTTP
    js-flot js-jquery js-dgtable
  ];

  root = nix-gitignore.gitignoreSource [] ../shake;
in
lib.pipe (labHaskellPackages.callCabal2nix "1lab-shake" root {}) [
  (hlib.addBuildTools [ removeReferencesTo ])
  (hlib.overrideCabal (drv: {
    postInstall = drv.postInstall or "" + ''
      find "$out/bin" -exec remove-references-to ${lib.concatMapStringsSep " " (x: "-t ${lib.escapeShellArg x}") forbiddenRefs} '{}' +
    '';
    disallowedRequisites = forbiddenRefs;
  }))
]
