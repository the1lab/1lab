[![Discord](https://img.shields.io/discord/914172963157323776?label=Discord&logo=discord)](https://discord.gg/NvXkUVYcxV)
[![Build 1Lab](https://github.com/plt-amy/cubical-1lab/actions/workflows/build.yml/badge.svg)](https://github.com/plt-amy/cubical-1lab/actions/workflows/build.yml)

# [1Lab](https://cubical.1lab.dev)

A formalised, cross-linked reference resource for mathematics done in
Homotopy Type Theory. Unlike the HoTT book, the 1lab is not a “linear”
resource: Concepts are presented as a directed graph, with links
indicating dependencies.

# Building

Here's how you can build --- and work on --- the web parts of the 1lab.

## Using Docker

An Arch Linux-based Docker container is provided which contains all the
dependencies necessary for building the 1lab, including the font files
required for a complete deployment. Since this container is on the
registry, we can do a one-line build of the 1Lab as follows:

```bash
% docker run -it -v $PWD:/workspace docker.io/pltamy/1lab:latest /bin/bash -i
$ 1lab-shake all -j         # build everything
$ bash support/make-site.sh # copy everything into place
```

After this, the directory `_build/site` will have everything in place
for use as the HTTP root of a static site to serve the 1Lab.

## Using Nix

If you run NixOS, or have the Nix package manager installed, you can use
the provided `default.nix` file to build a complete, reproducible
deployment of the 1Lab. This has the benefit of also providing
`nix-shell` support for immediately setting up an environment for
development which supports compilation of the HTML and SVG files, in
addition to the Agda.

To build, invoke `nix build`. The result will be linked as `result` as
usual. This directory tree can then be copied or used directly as the
root for a web server, since all the required dependencies are copied
into place.

```bash
$ nix build
```

The `buildInputs` to `default.nix` _don't_ include Stack, so you'll have
to use `runghc` to build incrementally:

```bash
$ runghc ./Shakefile.hs all -j
```

## Directly

If you're feeling brave, you can try to replicate one of the build
environments above. You will need:

- A Haskell package manager (either cabal or stack);

- Pandoc, preferably installed from the same Haskell package manager. No
specific version of Pandoc is required, but the version you choose is
required to match what your Haskell package manager will install for
pandoc-types;

- A working LaTeX installation (TeXLive, etc) with the packages
`tikz-cd` (depends on `pgf`), `mathpazo`, `xcolor`, `preview`, and
`standalone` (depends on `varwidth` and `xkeyval`);

- [Rubber] (for `rubber`);
- [Poppler] (for `pdftocairo`);
- [`libsass`] (for `sassc`);
- The [KaTeX] executable `katex` in your `$PATH`;
- The tools [agda-fold-equations] and [agda-reference-filter], which are
Cabal packages and can be installed however you prefer

- If you're using Stack, that's all. If using cabal-install, you're
going to need the following Haskell packages:
  + shake
  + tagsoup
  + uri-encode

[Rubber]: https://github.com/petrhosek/rubber
[Poppler]: https://poppler.freedesktop.org/
[KaTeX]: https://katex.org
[agda-fold-equations]: https://git.amelia.how/amelia/agda-fold-equations.git
[agda-reference-filter]: https://git.amelia.how/amelia/agda-reference-filter.git
[`libsass`]: https://www.google.com/search?client=firefox-b-d&q=sassc

If everything is set up properly, the following command should work to
produce the compiled HTML, SVG and CSS files in `_build/html`. You can
then follow either the `support/make-site.sh` script or the
`installPhase` in `default.nix` to work out how to acquire & set up the
rest of the static assets.

```bash
$ ./Shakefile.hs all -j        # (using stack)
$ runghc ./Shakefile.hs all -j # (using cabal-install)
```