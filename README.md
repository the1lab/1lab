[![Discord](https://img.shields.io/discord/914172963157323776?label=Discord&logo=discord)](https://discord.gg/Zp2e8hYsuX)
[![Build 1Lab](https://github.com/the1lab/1lab/actions/workflows/build.yml/badge.svg)](https://github.com/the1lab/1lab/actions/workflows/build.yml)

# [1Lab](https://1lab.dev)

A formalised, cross-linked reference resource for mathematics done in
Homotopy Type Theory. Unlike the HoTT book, the 1lab is not a “linear”
resource: Concepts are presented as a directed graph, with links
indicating dependencies.

# Building

Building the 1Lab is a rather complicated task, which has led to a lot
of homebrew infrastructure being developed for it. We build against a
specific build of Agda (see the `rev` field in
`support/nix/dep/Agda/github.json`), and there are also quite a few
external dependencies (e.g. pdftocairo, katex). The recommended way of
building the 1Lab is using Nix.

As a quick point of reference, `nix-build` will type-check and compile
the entire thing, and copy the necessary assets to the right locations.
The result will be linked as `./result`, which can then be used to serve
a website:

```bash
$ nix-build
$ python -m http.server --directory result
```

Note that using Nix to build the website takes around ~20-30 minutes,
since it will type-check the entire codebase from scratch every time.
For interactive development, `nix-shell` will give you a shell with
everything you need to hack on the 1Lab, including Agda and the
pre-built Shakefile as `1lab-shake`:

```bash
$ 1lab-shake all -j
```

Since `nix-shell` will load the derivation steps as environment
variables, you can use something like this to copy the static assets
into place:

```bash
$ eval "$installPhase"
$ python -m http.server --directory _build/site
```

To hack on a file continuously, you can use "watch mode", which will
attempt to only check and build the changed file.

```
$ 1lab-shake all -w
```

Additionally, since the validity of the Agda code is generally upheld by
`agda-mode`, you can use `--skip-agda` to only build the prose. Note
that this will disable checking the integrity of link targets, the
translation of `` `ref`{.Agda} `` spans, and the code blocks will be
right ugly.

Our build tools are routinely built for x86_64-linux and uploaded to
Cachix. If you have the Cachix CLI installed, simply run `cachix use
1lab`. Otherwise, add the following to your Nix configuration:

```
substituters = https://1lab.cachix.org
trusted-public-keys = 1lab.cachix.org-1:eYjd9F9RfibulS4OSFBYeaTMxWojPYLyMqgJHDvG1fs=
```

If you ever need to work on the Shakefile itself, `nix-shell -A shakefile`
will give you a shell with all the required Haskell dependencies and a
working Haskell Language Server installation. You can then use
`cabal run 1lab-shake -- all -j` to build the Shakefile and the 1Lab.

## Directly

If you're feeling brave, you can try to replicate one of the build
environments above. You will need:

- The `cabal-install` package manager. Using `stack` is no longer supported.

- A working LaTeX installation (TeXLive, etc) with the packages
  listed in `default.nix` (see `our-texlive`).

- [Poppler](https://poppler.freedesktop.org/) (for `pdftocairo`);
- [Dart Sass](https://github.com/sass/dart-sass) (for `sass`);
- [Node](https://nodejs.org/en/) + required Node modules. Run `npm ci` to install those.

You can then use cabal-install to build and run our specific version of
Agda and our Shakefile. Follow the instructions in `cabal.project` to
pin Agda to the appropriate version, then run:

```bash
$ cabal install Agda -foptimise-heavily
# This will take quite a while!

$ cabal run 1lab-shake -- -j --skip-agda all
# the double dash separates cabal-install's arguments from our
# shakefile's.
```

To finish building the website, you will also need to manually install
the required assets: see the `installPhase` in `default.nix`.
