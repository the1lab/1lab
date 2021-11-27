# [Cubical 1lab](https://cubical.1lab.dev)

A section of the 1lab dedicated to mathematics done in Homotopy Type
Theory.

## Building

In addition to Pandoc, KaTeX, sass, [rubber], pdftocairo, and Lua,
you'll need [`agda-reference-filter`] and [`agda-fold-equations`] in
your PATH, so download and install those:

[rubber]: https://github.com/petrhosek/rubber

[`agda-reference-filter`]: https://git.amelia.how/amelia/agda-reference-filter

[`agda-fold-equations`]: https://git.amelia.how/amelia/agda-fold-equations

```bash
% git clone https://git.amelia.how/amelia/agda-reference-filter.git
% cd agda-reference-filter
% stack install
% cd ..

% git clone https://git.amelia.how/amelia/agda-fold-equations.git
% cd agda-fold-equations
% stack install

# you can get rid of the sources now
```

Now you can build the 1lab pages & its part of the CSS:

```bash
% ./Shakefile.hs all -j$(nproc)
```

A complete deployment also redistributes parts of the following free
software projects:

* KaTeX CSS & fonts: put `katex.min.css` under `_build/html/css/`, and
the KaTeX font files under `_build/html/css/fonts`.

* Iosevka (as iosevk-abbie): Either build it yourself or get mine
[here](https://files.amelia.how/3OYp.xz), as a xz'd tar. Put the `woff2`
and `ttf` directories of the tar under static/.

## Contributing

Before submitting a merge request, please check the items below:

- [ ] The imports are sorted (use `find -type f -name \*.agda -or -name \*.lagda.md | xargs support/sort-imports.hs`)

- [ ] All code blocks have "agda" as their language. This is so that
tools like Tokei can report accurate line counts for proofs vs. text.

- [ ] Proofs are explained to a satisfactory degree; This is subjective,
of course, but proofs should be comprehensible to a hypothetical human
whose knowledge is limited to a working understanding of non-cubical
Agda, and the stuff your pages link to.

The following items are encouraged, but optional:

- [ ] If you feel comfortable, add yourself to the Authors page! Add a
profile picture that's recognisably "you" under support/pfps; The
picture should be recognisable at 128x128px, should look good in a
squircle, and shouldn't be more than 200KiB.

- [ ] If your contribution makes mention of a negative statement, but
does not prove the negative (perhaps because it would distract from the
main point), consider adding it to the counterexamples folder.

- [ ] If a proof can be done in both "cubical style", and "book HoTT
style", and you have the energy to do both, consider doing both!
However, it is **completely file** to only do one! For instance, I
(Amélia) am much better at writing proofs "book-style".