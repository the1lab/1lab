<!--
```agda
open import Cat.Displayed.Cartesian.Indexing
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning
import Cat.Displayed.Morphism
```
-->

```agda
module Cat.Displayed.GenericObject
  {o ℓ o' ℓ'} {B : Precategory o ℓ}
  (E : Displayed B o' ℓ')
  where
```

<!--
```agda
open Precategory B
open Cat.Displayed.Morphism E
open Cat.Displayed.Reasoning E
open Displayed E
open Functor
```
-->

# Generic objects

There are 2 perspectives one can take on generic objects. The first is a
purely logical one: generic objects provide us a tool for giving
categorical models of higher order logics. The second perspective is
that generic objects are a categorical way of describing the size of
fibrations, and their ability to be internalized in the base category.
We shall use both perspectives interchangeably!

::: warning
The terminology surrounding generic objects is a bit of a disaster.
What we refer to as a generic object is referred to as a
*weak* generic object in [@Jacobs:2001]. However, we follow the
terminology set out in [@Sterling:2023], as generic objects in the sense
of Jacobs are quite rare.
:::

With that caveat out of the way, we define a generic object to be some
object $T : \cE_{U}$ with the property that for any $X' : \cE_{X}$, we
have a (not necessarily unique) cartesian map $X' \to T$. Note that this
means that generic objects are a **structure** in a fibration!

```agda
record Generic-object {t} (t' : Ob[ t ]) : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
  no-eta-equality
  field
    classify  : ∀ {x} → (x' : Ob[ x ]) → Hom x t
    classify' : ∀ {x} → (x' : Ob[ x ]) → Hom[ classify x' ] x' t'
    classify-cartesian : ∀ {x} (x' : Ob[ x ])
                       → is-cartesian E (classify x') (classify' x')

  module classify-cartesian {x} (x' : Ob[ x ]) = is-cartesian (classify-cartesian x')
```

The intuition for this definition is that if $\cE$ has a generic object,
then every object of $\cE$ arises as a reindexing of $T$ along *some*
morphism in the base.

If we think of $\cE$ as some sort of logic over some syntactic category,
then a generic object behaves like $\mathrm{Prop}$, the type of
propositions. To see why, recall that an object $\cE_{\Gamma}$ over a
classifying category is a proposition in ranging over some free
variables of type $\Gamma$. The classifying map in the base yields a
substitution $\Gamma \to \mathrm{Prop}$, or in other words, a term of
type $\mathrm{Prop}$ in context $\Gamma$.  Furthermore, the classifying
map upstairs gives an implication between the original proposition in
$\cE_{\Gamma}$ and a proof of the corresponding element of
$\mathrm{Prop}$.

The size-based perspective on generic objects hinges on the fact that
[the family fibration on $\cC$ has a generic object if and only if $\cC$
is equivalent to a small, strict category][fam-generic].  Fibred
structure in the family fibration corresponds to structure in $\cC$, so
we can see the generic objects as a generalization of both a strictness
and size condition.

[fam-generic]: Cat.Displayed.Instances.Family.html#generic-objects

With this size-based perspective in mind, we say that a [[displayed
category]] is **globally small** if it has a generic object.

```agda
record Globally-small : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
  no-eta-equality
  field
    {U} : Ob
    Gen : Ob[ U ]
    has-generic-ob : Generic-object Gen

  open Generic-object has-generic-ob public
```

<!--
```agda
module _ (fib : Cartesian-fibration E) where
  open Cartesian-fibration fib
```
-->

We can also prove the aforementioned characterisation in terms of base
changes: If there exists an object $t' \liesover t$, such that, for
every $x' \liesover x$, there is a map $u : x \to t$ exhibiting $x'
\cong u^*(t')$ --- then $t'$ is a generic object. The quantifier
complexity of this sentence is a bit high, so please refer to the code:

```agda
  vertical-iso→Generic-object
    : ∀ {t} (t' : Ob[ t ])
    → (∀ {x} (x' : Ob[ x ])
      → Σ[ u ∈ Hom x t ]
         (base-change E fib u .F₀ t' ≅↓ x'))
    → Generic-object t'

```

<!--
```agda
  vertical-iso→Generic-object {t} t' viso = gobj where
    open Generic-object
    open has-lift

    module viso {x} (x' : Ob[ x ]) = _≅[_]_ (viso x' .snd)

    gobj : Generic-object t'
    gobj .classify x' = viso x' .fst
    gobj .classify' x' =
      hom[ idr _ ] (has-lift.lifting _ t' ∘' viso.from' x')
    gobj .classify-cartesian x' .is-cartesian.universal m h' =
      hom[ idl _ ] (viso.to' x' ∘' universal (viso x' .fst) t' m h')
    gobj .classify-cartesian x' .is-cartesian.commutes m h' =
      hom[] (lifting _ _ ∘' viso.from' x') ∘' hom[] (viso.to' x' ∘' universal _ _ _ _) ≡˘⟨ split _ _ ⟩
      hom[] ((lifting _ _ ∘' viso.from' x') ∘' (viso.to' x' ∘' universal _ _ _ _))     ≡⟨ weave _ _ refl (cancel-inner[] _ (viso.invr' x')) ⟩
      hom[] (lifting _ _ ∘' universal _ _ _ _)                                         ≡⟨ shiftl _ (has-lift.commutes _ _ _ _) ⟩
      h' ∎
    gobj .classify-cartesian x' .is-cartesian.unique {m = m} {h' = h'} m' p =
      m'                                                            ≡⟨ shiftr (sym (idl _) ∙ sym (idl _)) (insertl' _ (viso.invl' x')) ⟩
      hom[] (viso.to' x' ∘' viso.from' x' ∘' m')                    ≡⟨ reindex _ _ ∙ sym (hom[]-∙ (idl _) (idl _))  ∙ ap hom[] (unwhisker-r (idl _) (idl _)) ⟩
      hom[] (viso.to' x' ∘' ⌜ hom[ idl _ ] (viso.from' x' ∘' m') ⌝) ≡⟨ ap! (unique _ _ _ (whisker-r _ ∙ assoc[] ∙ unwhisker-l (ap (_∘ m) (idr _)) _ ∙ p)) ⟩
      hom[] (viso.to' x' ∘' universal _ _ _ h') ∎
```
-->

## Skeletal generic objects

We say that a generic object $t'$ is **skeletal** if the classifying map
in the base category is unique: if $u : x \to t$ underlies a Cartesian
map $x' \to_u t'$, then it must be the map coming from the generic object
structure of $t'$.

This condition is quite strong: for instance, the family fibration of a
[[strict category]] $\cC$ has a skeletal generic object if and only if
$\cC$ is [skeletal].^[See [here][skeletal-generic-object] for a proof.]

[skeletal-generic-object]: Cat.Displayed.Instances.Family.html#skeletal-generic-objects
[skeletal]: Cat.Skeletal.html

```agda
is-skeletal-generic-object : ∀ {t} {t' : Ob[ t ]} → Generic-object t' → Type _
is-skeletal-generic-object {t} {t'} gobj =
  ∀ {x} {x' : Ob[ x ]} {u : Hom x t} {f' : Hom[ u ] x' t'}
  → is-cartesian E u f' → u ≡ classify x'
  where open Generic-object gobj
```

::: warning
[@Jacobs:2001] refers to "skeletal generic objects" as simply "generic objects".
:::

<!--
```agda
is-skeletal-generic-object-is-prop
  : ∀ {t} {t' : Ob[ t ]} {gobj : Generic-object t'}
  → is-prop (is-skeletal-generic-object gobj)
is-skeletal-generic-object-is-prop = hlevel!
```
-->

## Gaunt generic objects

A generic object is **gaunt** if the classifying maps _themselves_ are
unique. This condition expands on that of skeletality: if $u' : x' \to_u
t'$ is a Cartesian map into the generic object $t'$, then not only must
$u$ be generated by the structure we have equipped $t'$ with, but $u'$
must, as well.

We can also expand on what this means for the family fibration:
$\rm{Fam}({\cC})$ has a gaunt generic object if and only if $\cC$ is itself
[gaunt] (See [here](Cat.Displayed.Instances.Family.html#gaunt-generic-objects)
for the proof).

[gaunt]: Cat.Gaunt.html

<!--
```agda
record is-gaunt-generic-object
  {t} {t' : Ob[ t ]}
  (gobj : Generic-object t')
  : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
  no-eta-equality
  open Generic-object gobj
```
-->

```agda
  field
    classify-unique : is-skeletal-generic-object gobj
    classify-unique'
      : ∀ {x} {x' : Ob[ x ]} {u : Hom x t} {f' : Hom[ u ] x' t'}
      → (cart : is-cartesian E u f')
      →  f' ≡[ classify-unique cart ] classify' x'
```

<!--
```agda
gaunt-generic-object→skeletal-generic-object
  : ∀ {t} {t' : Ob[ t ]} {gobj : Generic-object t'}
  → is-gaunt-generic-object gobj → is-skeletal-generic-object gobj
gaunt-generic-object→skeletal-generic-object =
  is-gaunt-generic-object.classify-unique
```
-->

::: warning
[@Jacobs:2001] refers to "gaunt generic objects" as "strong generic objects".
:::

<!--
```agda
is-gaunt-generic-object-is-prop
  : ∀ {t} {t' : Ob[ t ]} {gobj : Generic-object t'}
  → is-prop (is-gaunt-generic-object gobj)
is-gaunt-generic-object-is-prop = Iso→is-hlevel 1 eqv $
  Σ-is-hlevel 1 hlevel! λ _ →
  Π-is-hlevel' 1 λ _ → Π-is-hlevel³' 1 λ _ _ _ →
  Π-is-hlevel 1 λ _ →
  PathP-is-hlevel' 1 (Hom[ _ ]-set _ _) _ _
  where unquoteDecl eqv = declare-record-iso eqv (quote is-gaunt-generic-object)
```
-->
