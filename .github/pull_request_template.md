# Description

Please include a quick description of the changes here.

## Checklist

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
However, it is **completely fine** to only do one! For instance, I
(Amélia) am much better at writing proofs "book-style".
