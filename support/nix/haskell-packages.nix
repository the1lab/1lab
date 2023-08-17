pkgs: super:
let
  thunkSource = (import ./dep/nix-thunk { inherit pkgs; }).thunkSource;
  noJunk = x: pkgs.haskell.lib.overrideCabal x {
    doCheck = false;
    doHaddock = false;
    testHaskellDepends = [];
  };
  noProfile = x: pkgs.haskell.lib.overrideCabal x {
    enableExecutableProfiling = false;
    enableLibraryProfiling = false;
  };
in
  {
    # Can't just override all Haskell packages because callCabal2nix
    # somehow depends on mime-types
    labHaskellPackages = super.haskell.packages.ghc943.override (old: {
      overrides = self: super: {
        Agda = noProfile (noJunk (super.callCabal2nixWithOptions "Agda" (thunkSource ./dep/Agda) "-f optimise-heavily" {}));


        # Currently broken (set to 0 so other packages which depend on
        # it explode)
        hspec-contrib         = 0;
        hspec-core            = 0;

        # Depend on hspec for their test suites. Just don't test them
        JuicyPixels           = noJunk super.JuicyPixels;
        doctest               = noJunk super.doctest;
        shelly                = noJunk super.shelly;
        hls-graph             = noJunk super.hls-graph;

        pandoc                = noJunk (self.callCabal2nix "pandoc" (thunkSource ./dep/pandoc) {});
        pandoc-types          = noJunk (self.callCabal2nix "pandoc-types" (thunkSource ./dep/pandoc-types) {});
        commonmark            = noJunk (self.callCabal2nix "commonmark" ((thunkSource ./dep/commonmark-hs) + "/commonmark") {});
        commonmark-extensions = noJunk (self.callCabal2nix "commonmark-extensions" ((thunkSource ./dep/commonmark-hs) + "/commonmark-extensions") {});
        commonmark-pandoc     = noJunk (self.callCabal2nix "commonmark-pandoc" ((thunkSource ./dep/commonmark-hs) + "/commonmark-pandoc") {});
        texmath               = noJunk (self.callCabal2nix "texmath" (thunkSource ./dep/texmath) {});
        citeproc              = noJunk (self.callCabal2nix "citeproc" (thunkSource ./dep/citeproc) {});
        doclayout             = noJunk (self.callCabal2nix "doclayout" (thunkSource ./dep/doclayout) {});
        doctemplates          = noJunk (self.callCabal2nix "doctemplates" (thunkSource ./dep/doctemplates) {});
        gridtables            = noJunk (self.callCabal2nix "gridtables" (thunkSource ./dep/gridtables) {});
        jira-wiki-markup      = noJunk (self.callCabal2nix "jira-wiki-markup" (thunkSource ./dep/jira-wiki-markup) {});
        mime-types            = noJunk (self.callCabal2nix "mime-types" ((thunkSource ./dep/wai) + "/mime-types") {});
        skylighting           = noJunk (pkgs.haskell.lib.overrideCabal
          (self.callCabal2nix "skylighting" ((thunkSource ./dep/skylighting) + "/skylighting") {})
          {
            preConfigure = ''
            rm changelog.md
            cp ${((thunkSource ./dep/skylighting) + "/changelog.md")} .
            ${self.skylighting-core}/bin/skylighting-extract ${((thunkSource ./dep/skylighting) + "/skylighting-core/xml")}
            '';
          });
        skylighting-format-ansi       = noJunk (self.callCabal2nix "skylighting-format-ansi" ((thunkSource ./dep/skylighting) + "/skylighting-format-ansi") {});
        skylighting-format-blaze-html = noJunk (self.callCabal2nix "skylighting-format-blaze-html" ((thunkSource ./dep/skylighting) + "/skylighting-format-blaze-html") {});
        skylighting-format-context    = noJunk (self.callCabal2nix "skylighting-format-context" ((thunkSource ./dep/skylighting) + "/skylighting-format-context") {});
        skylighting-format-latex      = noJunk (self.callCabal2nix "skylighting-format-latex" ((thunkSource ./dep/skylighting) + "/skylighting-format-latex") {});
        skylighting-core              = noJunk
          (self.callCabal2nixWithOptions "skylighting-core" ((thunkSource ./dep/skylighting) + "/skylighting-core") "-fexecutable" {});
      };
    });
  }
