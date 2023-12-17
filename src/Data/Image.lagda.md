<!--
```agda
{-# OPTIONS -vtc.def:10 -vtc.ip.boundary:30 #-}
open import 1Lab.Prelude

open import Data.Id.Base
open import Data.Bool
```
-->

```agda
module Data.Image where
```

# Images and replacement

The [image] of a function $f : A \to B$ is the subtype of $B$ where points
are [[merely]] equipped with a fibre of $f$. This has the expected
universal property: we can factor any $f$ into

$$
A \epi \im(f) \mono B\text{,}
$$

and $\im(f) \mono B$ is universal among factorisations of $f$ through a
subtype of its codomain.

[image]: 1Lab.HIT.Truncation.html#maps-into-sets

In general, we can consider images of arbitrary functions $f : A \to B$,
where $A$ is a $\ell_1$-small type, and $B$ is a $\ell_2$-small type;
This results in a type $\im f$, which, according to the rules for
assigning universe levels, lives in the  $(\ell_1 \sqcup \ell_2)$th
universe. While the rules are that way for good reasons, in this case,
they defy intuition: the type $\im f$, in a sense, is "at most the size
of $A$".

Can we do better? It turns out that we can! This generally goes by the
name of **type-theoretic replacement**, after Rijke [@Rijke:2017 §5]; in
turn, the name _replacement_ comes from the axiom of material set theory
saying the image of a set under a function is again set.^[Keep in mind
that material set theory says "is a set" in a very different way than we
do; They mean it about size.] Here we implement a slight generalization
of [Evan Cavallo's construction] in terms of higher induction-recursion.

[Evan Cavallo's construction]: https://github.com/agda/cubical/pull/972

We understand this construction as generalising the [first isomorphism
theorem] from the setting of algebraic structures^[A class which
includes $\Sets$, as models of the trivial theory] to the setting of
general types. Recall that the first isomorphism theorem says you can
compute $\im f$ as the quotient $A/\ker f$.[^ker]

[first isomorphism theorem]: Algebra.Group.Subgroup.html#the-first-isomorphism-theorem

[^ker]: The meaning of kernel we're using generalises slightly that of
groups, where a normal subgroup completely determines an equivalence
relation. Instead, we mean the _kernel pair_, the pullback of a morphism
along itself.

If we're working with sets, that's the end of it: We can define a
relation $x \sim y$ by $f(x) \sim f(y)$, which [can be made to] live in
the zeroth universe, so $A/\ker f$ lives in the same universe as $A$.
That's because, when working with sets, there are no coherence problems
to get stuck on: we can first define $A/\ker f$ as a higher inductive
type, then, separately, define the embedding $A/\ker f \mono B$.

[can be made to]: 1Lab.Resizing.html

However, in the case of general types, we would like the h-level of $\im
f$ to match that of $B$, so we certainly can't set-truncate.

Anyway, The next immediate attempt might be a type which looks like

<!--
```agda
private module Attempts where
```
-->

```agda
  data Im1 {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} (f : A → B)
        : Type (ℓa ⊔ ℓb) where
    inc  : A → Im1 f
    quot : ∀ x y → f x ≡ f y → inc x ≡ inc y
```

But this type isn't particularly well-behaved. For example, the
`Im1`{.Agda}-image of the identity map on the unit type is the circle.
This can be established by writing equivalences back and forth, but in
the interest of brevity (and our dependency graph), we show it has a
non-trivial path.

```agda
  Cover : Im1 {A = ⊤} {⊤} (λ { tt → tt }) → Type
  Cover (inc x)          = Bool
  Cover (quot tt tt _ i) = ua (not , not-is-equiv) i

  Im1-nontriv : subst Cover (quot tt tt refl) true ≡ false
  Im1-nontriv = refl
```

It's fairly common that defining higher inductive types like this will,
sometimes, introduce more paths than you might expect. For an analogy,
if we were interested in computing _propositional truncations_ instead,
our type `Im1`{.Agda} above would correspond to this "one-step
truncation":

```agda
  data Tr1 {ℓa} (A : Type ℓa) : Type ℓa where
    inc  : A → Tr1 A
    quot : (x y : A) → inc x ≡ inc y
```

And, investigating the case of truncations, we might come up with a
couple different fixes. One is to define a process that could be
_iterated_: each step adds new paths, and at the limit --- the
_sequential co_-limit --- we have our original type. This can be made to
work for the propositional truncation, and [@Rijke:2017]'s construction
of the image is similar in spirit.

But if we have _recursive_ higher inductive types, where the type being
defined can appear in the _arguments_ to its own path constructors, we
can sometimes do these constructions in a single big, recursive step.
That's the usual [[propositional truncation]]. A guiding, heuristic
principle would be to avoid "green slime": do not mention the
constructors of the type in the _endpoints_ of the path constructor.

Types without green slime are much more merciful than the judges of
coherence hell, because you don't have to match to apply the path
constructors, as you would in `Tr1`{.Agda}: If you have the arguments
handy, you can apply them _targeting_ arbitrary points. Lovely! But In
the image case, this still doesn't really work, because we don't want to
identify _arbitrary_ points. Our requirements are something like this:

1. A tractable description: finitely many constructors, and hopefully
"no more than a few". This guarantees that we can tell Agda Agda about
the construction and _actually work with it_, which is also important.

2. Without any green slime, to _hopefully_ avoid the coherent issues.

3. So that points from $a$ are identified in $\im f$ exactly how they
would be identified in $b$ under $f$.

If we _had_ such a type, we could define an [[embedding]] $f' : \im f
\mono B$, which tells us how to compute the path spaces in $\im f$: $(x
\equiv y) \simeq (f'(x) \equiv f'(y))$. In fact, since images are almost
entirely characterised by having such an embedding, we can use our
hypothetical $f'$ to rewrite the third bullet point:

3. With a constructor coherently mapping proofs of $f'(x) \equiv f'(y)$
to $x \equiv y$.

Also, note that, since we were trying to get a _smaller_ image, we can't
just use $B$'s path types: those live at the same universe as $B$. What
we can do instead is parametrise over an [[identity system]] on $B$, a
reflexive family of types $x \sim y$ which is equivalent to $x \equiv y$
but which might be smaller. So, our requirement on identifications
should be

3. With a constructor coherently mapping proofs of $f'(x) \sim f'(y)$ to
$x \equiv y$.

But, identity system or not, this is hopeless, right? We don't know how
to specify $\im f$ without first defining $f'$; and it makes no sense to
define $f'$ before its domain type. The only way forward would be to
somehow define them at the same time. That's impossible, right?

## Higher induction-recursion

It's actually totally possible to, at least in Agda, define higher
inductive types at the same time as we define pattern-matching functions
on them. And that's exactly what we'll do: specify $\im f$
higher-inductively _at the same time as_ we define $f' : \im f \mono b$
by recursion. Our three bullet points from before become the
specification of the inductive type!

```agda
module Replacement
    {ℓₐ ℓₜ ℓᵢ} {A : Type ℓₐ} {T : Type ℓₜ}
    {_∼_ : T → T → Type ℓᵢ} {rr : ∀ x → x ∼ x}
    (locally-small : is-identity-system _∼_ rr)
    (f : A → T)
  where

  private module ls = Ids locally-small

  data Image : Type (ℓₐ ⊔ ℓᵢ)
  embed : Image → T

  data Image where
    inc  : A → Image
    quot : ∀ {r r'} → embed r ∼ embed r' → r ≡ r'

  embed (inc a)     = f a
  embed (quot p i)  = locally-small .to-path p i
```

And, having used inductive-recursion to tie the dependency knot, we're
actually done: the construction above is coherent enough, _even if_ it
looks like the `quot`{.Agda} constructor only says that `embed`{.Agda}
is an injection. We can use the algebraic properties of identity systems
to show that it's actually a proper embedding:

```agda
  embed-is-embedding' : ∀ x → is-contr (fibre embed (embed x))
  embed-is-embedding' x .centre = x , refl
  embed-is-embedding' x .paths (y , q) =
    Σ-pathp (quot (ls.from (sym q))) (commutes→square coh)
    where abstract
      coh : ls.to (ls.from (sym q)) ∙ q ≡ refl ∙ refl
      coh = ap (_∙ q) (ls.ε (sym q)) ·· ∙-invl q ·· sym (∙-idl refl)

  embed-is-embedding : is-embedding embed
  embed-is-embedding = embedding-lemma embed-is-embedding'
```

And it's possible to pull back the identity system on $b$ to one on $\im
f$, to really drive home the point that points in the image are
identified precisely through their identification, under $f$, in the
codomain.

```agda
  Image-identity-system : is-identity-system (λ x y → embed x ∼ embed y) (λ _ → rr _)
  Image-identity-system = pullback-identity-system locally-small
    (embed , embed-is-embedding)
```

<!--
```agda
  Image-is-hlevel : ∀ n → is-hlevel T (suc n) → is-hlevel Image (suc n)
  Image-is-hlevel n = embedding→is-hlevel n embed-is-embedding
```
-->

As usual with these things, we can establish properties of
`Image`{.Agda} without caring about the higher constructors.

```agda
  Image-elim-prop
    : ∀ {ℓ'} {P : Image → Type ℓ'}
    → (∀ x → is-prop (P x))
    → (∀ x → P (inc x))
    → ∀ x → P x
  Image-elim-prop pprop pinc (inc x) = pinc x
  Image-elim-prop pprop pinc (quot {x} {y} p i) =
    is-prop→pathp (λ i → pprop (quot p i))
      (Image-elim-prop pprop pinc x)
      (Image-elim-prop pprop pinc y) i
```

From which surjectivity follows immediately:

```agda
  inc-is-surjective : is-surjective inc
  inc-is-surjective = Image-elim-prop (λ _ → squash) (λ x → inc (x , refl))
```

## Comparison

We define a "comparison" map from the resized image to the "ordinary"
image. This map is a bit annoying to define, and it relies on being able
to easily map from the `Image`{.Agda} into propositions. It's
definitional that projecting from `Image→image`{.Agda} gives our
`embed`{.Agda}ding, since that's how we _define_ the map.

```agda
  Image→image : Image → image f
  Image→image x .fst = embed x
  Image→image x .snd =
    Image-elim-prop {P = λ x → ∥ fibre f (embed x) ∥} (λ _ → squash)
      (λ x → inc (x , refl))
      x
```

Establishing that `Image→image`{.Agda} is an equivalence is one of the
rare cases where it's easier to show that it has contractible fibres.
That's because we can eliminate the propositional truncation as the
first step, and deal only with untruncated data from then on.

```agda
  Image→image-is-equiv : is-equiv Image→image
  Image→image-is-equiv .is-eqv (x , p) =
    ∥-∥-elim {P = λ p → is-contr (fibre Image→image (x , p))}
      (λ _ → is-contr-is-prop)
      (λ { (i , p) → J
        (λ x p → is-contr (fibre Image→image (x , inc (i , p))))
        (work' i) p })
      p
    where
      work' : (f⁻¹x : A) → is-contr (fibre Image→image (f f⁻¹x , inc (_ , refl)))
      work' f⁻¹x .centre = inc f⁻¹x , refl -- inc f⁻¹x , refl
```

Contracting the fibres is where we get some mileage out of having gotten
the green slime out of `quot`{.Agda}. We have to show $f^{-1}(x) = i$,
as elements of the image, but we have an assumption that
$\mathrm{embed}(i) = ff^{-1}(x)$, which, under `quot`{.agda}, is exactly
what we need.

```agda
      work' f⁻¹x .paths (i , α) = Σ-pathp (quot (ls.from (sym (ap fst α)))) $
        Σ-prop-square (λ _ → squash) $ commutes→square $
          (ap₂ _∙_ (ls.ε (sym (ap fst α))) refl ∙ ∙-invl _ ∙ sym (∙-idl _))
```
