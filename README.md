# [Cubical 1lab](https://cubical.1lab.dev)

A section of the 1lab dedicated to mathematics done in Homotopy Type
Theory.

## Building

In addition to [Pandoc], KaTeX, sassc, [rubber], pdftocairo, and Lua,
you'll need [`agda-reference-filter`] and [`agda-fold-equations`] in
your PATH, so download and install those:

[rubber]: https://github.com/petrhosek/rubber

[`agda-reference-filter`]: https://git.amelia.how/amelia/agda-reference-filter

[`agda-fold-equations`]: https://git.amelia.how/amelia/agda-fold-equations

```
% git clone https://git.amelia.how/amelia/agda-reference-filter.git
% cd agda-reference-filter
% stack install
# you can get rid of the source now
```

Now you can build the 1lab pages & its part of the CSS:

```
% ./Shakefile.hs all -j$(nproc)
```

A complete deployment also includes the following free software projects:

* KaTeX CSS & fonts: put `katex.min.css` under `_build/html/css/`, and
the KaTeX font files under `_build/html/css/fonts`

* Iosevka (as iosevk-abbie): Either build it yourself or get mine
[here](https://files.amelia.how/3OYp.xz), as a xz'd tar. Put the `woff2`
and `ttf` directories of the tar under static/.