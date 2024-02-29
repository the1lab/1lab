<!--
```agda
open import Cat.Functor.FullSubcategory
open import Cat.Diagram.Equaliser
open import Cat.Diagram.Initial
open import Cat.Diagram.Pushout
open import Cat.Instances.Comma
open import Cat.Instances.Slice
open import Cat.Diagram.Image
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Equaliser.RegularMono {o ℓ} (C : Precategory o ℓ) where
```

<!--
```agda
open Cat.Reasoning C
open Initial
open ↓Obj
open ↓Hom
open /-Obj
open /-Hom
private variable a b : Ob
```
-->

# Regular monomorphisms

A **regular monomorphism** is a morphism that behaves like an
_embedding_, i.e. it is an isomorphism onto its [[image]]. Since images
of arbitrary morphisms do not exist in every category, we must find a
definition which implies this property but only speaks diagrammatically
about objects directly involved in the definition.

The definition is as follows: A **regular monomorphism** $f : a \mono b$
is an [[equaliser]] of some pair of arrows $g, h : b \to c$.

```agda
record is-regular-mono (f : Hom a b) : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    {c}       : Ob
    arr₁ arr₂ : Hom b c
    has-is-eq : is-equaliser C arr₁ arr₂ f

  open is-equaliser has-is-eq public
```

From the definition we can directly conclude that regular monomorphisms
are in fact monomorphisms:

```agda
  is-regular-mono→is-mono : is-monic f
  is-regular-mono→is-mono = is-equaliser→is-monic C _ has-is-eq

open is-regular-mono using (is-regular-mono→is-mono) public
```

## Effective monomorphisms

Proving that a map $f$ is a regular monomorphism involves finding two
maps which it equalises, but if $\cC$ is a category with [pushouts],
there is often a canonical choice: The **cokernel pair** of $f$, that
is, the pushout of $f$ along with itself. Morphisms which a) have a
cokernel pair and b) equalise their cokernel pair are called **effective
monomorphisms**.

[pushouts]: Cat.Diagram.Pushout.html

```agda
record is-effective-mono (f : Hom a b) : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    {cokernel}       : Ob
    i₁ i₂            : Hom b cokernel
    is-cokernel-pair : is-pushout C f i₁ f i₂
    has-is-equaliser : is-equaliser C i₁ i₂ f
```

Every effective monomorphism is a regular monomorphism, since it
equalises the inclusions of its cokernel pair.

```agda
  is-effective-mono→is-regular-mono : is-regular-mono f
  is-effective-mono→is-regular-mono = rm where
    open is-regular-mono
    rm : is-regular-mono f
    rm .c = _
    rm .arr₁ = _
    rm .arr₂ = _
    rm .has-is-eq = has-is-equaliser
```

If $f$ has a cokernel pair, and it is a regular monomorphism, then it is
also effective --- it is the equaliser of its cokernel pair.

```agda
is-regular-mono→is-effective-mono
  : ∀ {a b} {f : Hom a b}
  → Pushout C f f
  → is-regular-mono f
  → is-effective-mono f
is-regular-mono→is-effective-mono {f = f} cokern reg = mon where
  module f⊔f = Pushout cokern
  module reg = is-regular-mono reg
```

Let $f : a \mono b$ be the equaliser of $\rm{arr_1}, \rm{arr_2} : b \to
c$. By the universal property of the cokernel pair of $f$, we have a map
$\phi : B \sqcup_A B \to C$ such that $\phi \circ i_1 = \rm{arr_1}$ and
$\phi \circ i_2 = \rm{arr_2}$.

```agda
  phi : Hom f⊔f.coapex reg.c
  phi = f⊔f.universal reg.equal

  open is-effective-mono
  mon : is-effective-mono f
  mon .cokernel = f⊔f.coapex
  mon .i₁ = f⊔f.i₁
  mon .i₂ = f⊔f.i₂
  mon .is-cokernel-pair = f⊔f.has-is-po
  mon .has-is-equaliser = eq where
```

To show that $f$ also has the universal property of the equaliser of
$i_1, i_2$, suppose that $e\prime : E \to b$ also equalises the
injections. Then we can calculate:

$$
\rm{arr_1}e\prime = (\phi i_1)e\prime = (\phi i_2)e\prime = \rm{arr_2}e\prime
$$

So $e\prime$ equalises the same arrows that $f$ does, hence there is a
universal map $E \to a$ which commutes with "everything in sight":

```agda
    open is-equaliser
    eq : is-equaliser _ _ _ _
    eq .equal     = f⊔f.square
    eq .universal {F = F} {e' = e'} p = reg.universal p' where
      p' : reg.arr₁ ∘ e' ≡ reg.arr₂ ∘ e'
      p' =
        reg.arr₁ ∘ e'       ≡˘⟨ ap (_∘ e') f⊔f.i₁∘universal ⟩
        (phi ∘ f⊔f.i₁) ∘ e' ≡⟨ extendr p ⟩
        (phi ∘ f⊔f.i₂) ∘ e' ≡⟨ ap (_∘ e') f⊔f.i₂∘universal ⟩
        reg.arr₂ ∘ e'       ∎
    eq .factors = reg.factors
    eq .unique = reg.unique
```

If $f : A \to B$ has a canonical choice of pushout along itself, then it
suffices to check that it equalises those injections to show it is an
effective mono.

```agda
equalises-cokernel-pair→is-effective-mono
  : ∀ {a b} {f : Hom a b}
  → (P : Pushout C f f)
  → is-equaliser C (P .Pushout.i₁) (P .Pushout.i₂) f
  → is-effective-mono f
equalises-cokernel-pair→is-effective-mono P eq = em where
  open is-effective-mono
  em : is-effective-mono _
  em .cokernel = _
  em .i₁ = _
  em .i₂ = _
  em .is-cokernel-pair = P .Pushout.has-is-po
  em .has-is-equaliser = eq
```

## Images of regular monos

Let $f : A \mono B$ be an effective mono, or, in a category with
pushouts, a regular mono. We show that $f$ admits an [[image]] relative to
the class of regular monomorphisms. The construction of the image is as
follows: We let $\im f = A$ and factor $f$ as

$$ A \xto{\id} A \xmono{f} B $$

This factorisation is very straightforwardly shown to be universal, as
the code below demonstrates.

```agda
is-effective-mono→image
  : ∀ {a b} {f : Hom a b}
  → is-effective-mono f
  → M-image C (is-regular-mono , is-regular-mono→is-mono) f
is-effective-mono→image {f = f} mon = im where
  module eff = is-effective-mono mon

  itself : ↓Obj _ _
  itself .x = tt
  itself .y = restrict (cut f) eff.is-effective-mono→is-regular-mono
  itself .map = record { map = id ; commutes = idr _ }

  im : Initial _
  im .bot = itself
  im .has⊥ other = contr hom unique where
    hom : ↓Hom _ _ itself other
    hom .α = tt
    hom .β = other .map
    hom .sq = trivial!

    unique : ∀ x → hom ≡ x
    unique x = ↓Hom-path _ _ refl
      (ext (intror refl ∙ ap map (x .sq) ∙ elimr refl))
```

Hence the characterisation of regular monomorphisms given in the
introductory paragraph: In a category with pushouts, every regular
monomorphism "is an isomorphism" onto its image. In reality, _it gives
its own image_!
