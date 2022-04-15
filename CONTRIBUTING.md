Contributing
------------

Thanks for taking the time to contribute!

This file holds the conventions we use around the codebase, but they're
guidelines, and not strict rules: If you're unsure of something, hop on
[the Discord](https://discord.gg/NvXkUVYcxV) and ask there, or open [a
discussion thread](https://github.com/plt-amy/cubical-1lab/discussions)
if that's more your style.

### General guidelines

Use British spelling everywhere that it differs from American: Homotopy
fib**re**, fib**red** category, colo**u**red operad, etc --- both in
prose and in Agda. Keep prose paragraphs limited to 72 characters of
length. Prefer link anchors (Pandoc "reference links") to inline links.

### Agda code style

Agda code should be kept to less than 85 columns; This doesn't count
lines that include equational reasoning combinators (anything that's
delineated by a matching pair of `⟨⟩`), since those are folded away on
the website; Length counting for those lines stops at the first `⟨`
character.

Identifiers should be `kebab-case`, though other separators are allowed
when the context calls for them: `→` abbreviates the word "to" (and
similar), `≃` abbreviates "is equivalent to", `≡`, etc.  The first word
in type names should be capitalised; "Function" names should be all
lower case. Exceptions are made for proper nouns (Type is a proper
noun).

Prefer to write out identifiers longhand, rather than using
abbreviations, other than the following:

* "Cat" abbreviates category;
* "Iso" abbreviates isomorphism (either of types or of objects in a
category)
* "Equiv" abbreviates equivalence _of types_; Equivalence of
(pre)categories should be written out longhand.
* "hom" abbreviates homomorphism.

Type families valued in propositions, either defined as records,
functions or as truncated inductive types, should start with the word
`is`: `is-prop`, `is-set`, etc. Predicates should be written _after_
what they apply to: `Nat-is-set`, `is-prop-is-prop`,
`is-hlevel-is-prop`. Record fields indicating the truth of a predicate
should be prefixed `has-is-`, since Agda doesn't allow you to shadow
globals with record fields.

If possible, prove that things are valued in h-level n separately,
rather than defining maps into `n-Type`; This can't always be avoided
because of truncated HITs.

When eliminating out of a HIT like `Data.Set.Coequaliser`, put the
necessary equations in an `abstract` block; If everything defined for
that function is abstract, put `where abstract` into a single line, like
in `Algebra.Group.Ab.Free`:

```agda
    fold : (f : G → G' .fst) → Group-hom Grp G' f → G^ab → G' .fst
    fold f gh = Coeq-rec G'.has-is-set f l1
      where abstract
        l1 : ((x , y , z) : G × G × G) → f (x ⋆ y ⋆ z) ≡ f (x ⋆ z ⋆ y)
        l1 (x , y , z) =
```

**Everything should be literate**. Do not submit PRs with plain Agda
files!