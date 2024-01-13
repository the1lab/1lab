<!--
```agda
open import Cat.Functor.FullSubcategory
open import Cat.Diagram.Initial
open import Cat.Functor.Adjoint
open import Cat.Instances.Comma
open import Cat.Instances.Slice
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Image {o ℓ} (C : Precategory o ℓ) where
```

<!--
```agda
open Cat.Reasoning C
open Initial
open ↓Obj
open ↓Hom
open /-Obj
open /-Hom

private variable
  a b : Ob
  ℓ' : Level
```
-->

# Images {defines="image image-factorisation"}

Let $f : A \to B$ be an ordinary function between sets (or, indeed,
arbitrary types). Its **image** $\im f$ can be computed as the subset
$\{ b \in B : (\exists a)\ b = f(a) \}$, but this description does not
carry over to more general categories: More abstractly, we can say that
the image [[embeds into|embedding]] $B$, and admits a map from $A$ (in
material set theory, this is $f$ itself --- structurally, it is called
the
**corestriction** of $f$). Furthermore, these two maps _factor_ $f$, in
that:

$$
(A \xto{e} \im f \xmono{m} B) = (A \xto{f} B)
$$

While these are indeed two necessary properties of an _image_, they fail
to accurately represent the set-theoretic construction: Observe that,
e.g. for $f(x) = 2x$, we could take $\im f = \bb{N}$, taking $e = f$
itself and $m = \bb{N} \xmono{\id} \bb{N}$. This factoring
clearly recovers $f$, as $\id \circ f = f$. But by taking this as
the image, we've lost the information that $f$ lands in the evens!

We can refine the abstract definition by saying that, for a mono $\im f
\xmono{m} B$ to be _the_ image of $f$, it must be the _smallest_
subobject of $B$ through which $f$ factors --- given any other factoring
of $f = m' \circ e'$, we must have $m \sube m'$ in the proset of
subobjects of $B$, i.e. there exists some $k$ such that $m = m' \circ
k$.

In general categories, [[monomorphisms]] of $\cC$ may be the wrong notion
of "subobject" to use. For example, in topology, we'd rather talk about
the image which admits a _subspace inclusion_ onto $B$. We may expand
the definition above to work for an arbitrary subclass $M \sube
\rm{Mono}(\cC)$ of the monomorphisms of $C$, by requiring that the
$M$-image of $f$ be the smallest $M$-subobject through which $f$
factors.

Since keeping track of all the factorisations by hand would be fiddly,
we formalise the idea of image here using [comma categories], namely the
idea of [universal morphisms] as in the construction of adjoints. Fix a
morphism $f : a \to b$, and consider it as an object of the [slice
category] $\cC/b$.

[comma categories]: Cat.Instances.Comma.html
[universal morphisms]: Cat.Functor.Adjoint.html#universal-morphisms
[slice category]: Cat.Instances.Slice.html

For a given subclass of monomorphisms $M$, there is a full subcategory
of $\cC/b$ spanned by those maps in $M$ --- let us call it $M/b$
--- admitting an evident [[fully faithful]] inclusion $F : M/b \mono \cC/b$. An
**$M$-image of $f$** is a universal morphism from $f$ to $F$.

```agda
Class-of-monos : ∀ ℓ → Type _
Class-of-monos ℓ =
  Σ[ M ∈ (∀ {a b} → Hom a b → Type ℓ) ]
    (∀ {a b} {f : Hom a b} → M f → is-monic f)

M-image : ∀ {a b} → Class-of-monos ℓ' → Hom a b → Type _
M-image {a = a} {b} M f = Universal-morphism (cut f)
  (Forget-full-subcat
    {C = Slice C b}
    {P = (λ o → M .fst (o .map))})
```

**The** image is the $M$-image for $M$ = the class of all monomorphisms.

```agda
Image : ∀ {a b} → Hom a b → Type _
Image {b = b} f = Universal-morphism (cut f)
  (Forget-full-subcat {C = Slice C b} {P = is-monic ⊙ map})
```

## Friendly interface

Since this definition is incredibly abstract and indirect, we provide a
very thin wrapper module over `M-image`{.Agda} which unpacks the
definition into friendlier terms.

```agda
module M-Image {a b} {M : Class-of-monos ℓ'} {f : Hom a b} (im : M-image M f) where
```

The first thing to notice is that, being an initial object in the comma
category $f \swarrow F$, we have an object $(c, c \xmono{m} b)$ --- $c$
is the image object, and $m$ is the inclusion map:

```agda
  Im : Ob
  Im = im .bot .y .object .domain

  Im→codomain : Hom Im b
  Im→codomain = im .bot .y .object .map
```

Furthermore, this map is both an inclusion (since $M$ is a class of
monomorphisms), and an $M$-inclusion at that:

```agda
  Im→codomain-is-M : M .fst Im→codomain
  Im→codomain-is-M = im .bot .y .witness

  Im→codomain-is-monic : is-monic Im→codomain
  Im→codomain-is-monic = M .snd Im→codomain-is-M
```

So far, we've been looking at the "codomain" part of the object in the
comma category. We also have the "morphism" part, which provides our
(universal) factoring of $f$:

```agda
  corestrict : Hom a Im
  corestrict = im .bot .map .map

  image-factors : Im→codomain ∘ corestrict ≡ f
  image-factors = im .bot .map .commutes
```

This is also the _smallest_ factorisation, which takes quite a lot of
data to express. Let's see it:

Suppose we have

* Some other object $c$; and,
* An $M$-monomorphism $c \xmono{m} b$; and,
* A corestriction map $a \xto{i} c$; such that
* $m \circ i = f$.

Then we have a map $k : \im f \to c$ (written `im≤other-image`{.Agda} in
the code below), and the canonical inclusion $\im f \mono B$ factors
through $k$:

```agda
  universal
    : ∀ {c} (m : Hom c b) (M-m : M .fst m) (i : Hom a c)
    → m ∘ i ≡ f
    → Hom Im c
  universal m M i p = im .has⊥ obj .centre .β .map where
    obj : ↓Obj _ _
    obj .x = tt
    obj .y = restrict (cut m) M
    obj .map = record { map = i ; commutes = p }

  universal-factors
    : ∀ {c} {m : Hom c b} {M : M .fst m} {i : Hom a c}
    → {p : m ∘ i ≡ f}
    → m ∘ universal m M i p ≡ Im→codomain
  universal-factors {m = m} {M} {i} {p} = im .has⊥ _ .centre .β .commutes

  universal-commutes
    : ∀ {c} {m : Hom c b} {M : M .fst m} {i : Hom a c}
    → {p : m ∘ i ≡ f}
    → universal m M i p ∘ corestrict ≡ i
  universal-commutes {m = m} {ism} {i} {p} =
    M .snd ism _ _ (pulll universal-factors ·· image-factors ·· sym p)
```

<!--
```agda
module Image {a b} {f : Hom a b} (im : Image f) = M-Image {M = is-monic , λ x → x} im
```
-->
