```agda
open import Cat.Functor.Adjoint.Compose
open import Cat.Functor.Naturality
open import Cat.Functor.Properties
open import Cat.Functor.Adjoint
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning as Fr
import Cat.Reasoning as Cat

module Cat.Functor.Equivalence where
```

<!--
```agda
private variable
  o h : Level
  C D E : Precategory o h

private module _ {o ℓ} {C : Precategory o ℓ} where
  open Cat C using (_∘Iso_ ; _Iso⁻¹ ; invl ; invr) public
  open Cat.is-invertible C using (invl ; invr) public

open Functor hiding (op)
open _=>_ hiding (op)
```
-->

# Equivalences {defines="equivalence-of-categories equivalences-of-categories adjoint-equivalence equivalence-of-precategories"}

An adjunction $F \vdash G$ is an **adjoint equivalence**, or an
**equivalence of (pre)categories**, if the unit and counit natural
transformations are both [[natural isomorphisms]]. This immediately
implies that our adjoint pair $F \dashv G$ extends to an adjoint triple
$F \dashv G \dashv F$.

```agda
record adjunction-is-equivalence
    {F : Functor C D} {F⁻¹ : Functor D C}
    (F⊣F⁻¹ : F ⊣ F⁻¹)
  : Type (adj-level C D) where

  open _⊣_ F⊣F⁻¹ hiding (η ; ε) public

  field
    unit-iso   : ∀ x → Cat.is-invertible C (unit.η x)
    counit-iso : ∀ x → Cat.is-invertible D (counit.ε x)
```

The first thing we note is that having a natural family of invertible
morphisms gives isomorphisms in the respective functor categories:

```agda
  private
    [C,C] = Cat[ C , C ]
    [D,D] = Cat[ D , D ]

  F∘F⁻¹≅Id : Cat.Isomorphism [D,D] (F F∘ F⁻¹) Id
  F∘F⁻¹≅Id = Cat.invertible→iso [D,D]
    counit
    (invertible→invertibleⁿ _ counit-iso)

  Id≅F⁻¹∘F : Cat.Isomorphism [C,C] Id (F⁻¹ F∘ F)
  Id≅F⁻¹∘F = Cat.invertible→iso [C,C]
    unit (invertible→invertibleⁿ _ unit-iso)

  unit⁻¹   = Cat.from Id≅F⁻¹∘F
  counit⁻¹ = Cat.from F∘F⁻¹≅Id
```

<!--
```agda
  F⁻¹⊣F : F⁻¹ ⊣ F
  F⁻¹⊣F = adj' where
    module adj = _⊣_ F⊣F⁻¹
    open _⊣_

    module C = Cat C using (id ; _∘_ ; cancelr ; introl)
    module D = Cat D using (id ; _∘_ ; cancell ; intror)

    adj' : F⁻¹ ⊣ F
    adj' .unit   = counit⁻¹
    adj' .counit = unit⁻¹
    adj' .zig {a} = zig' where abstract
      p : unit⁻¹ .η (F⁻¹ · a) ≡ F⁻¹ .F₁ (adj.ε _)
      p =
        unit⁻¹ .η _                                      ≡⟨ C.introl adj.zag ⟩
        (F⁻¹ .F₁ (adj.ε _) C.∘ adj.η _) C.∘ unit⁻¹ .η _  ≡⟨ C.cancelr (unit-iso _ .invl) ⟩
        F⁻¹ .F₁ (adj.ε _)                                ∎

      zig' : unit⁻¹ .η (F⁻¹ · a) C.∘ F⁻¹ .F₁ (counit⁻¹ .η a) ≡ C.id
      zig' = ap₂ C._∘_ p refl ∙∙ sym (F⁻¹ .F-∘ _ _) ∙∙ ap (F⁻¹ .F₁) (counit-iso _ .invl) ∙ F⁻¹ .F-id

    adj' .zag {b} = zag' where abstract
      p : counit⁻¹ .η (F · b) ≡ F .F₁ (adj.η b)
      p =
        counit⁻¹ .η _                                  ≡⟨ D.intror adj.zig ⟩
        counit⁻¹ .η _ D.∘ adj.ε _ D.∘ F .F₁ (adj.η b)  ≡⟨ D.cancell (counit-iso _ .invr) ⟩
        F .F₁ (adj.η b)                                ∎

      zag' : F .F₁ (unit⁻¹ .η b) D.∘ counit⁻¹ .η (F · b) ≡ D.id
      zag' = ap₂ D._∘_ refl p ∙∙ sym (F .F-∘ _ _) ∙∙ ap (F .F₁) (unit-iso _ .invr) ∙ F .F-id

  inverse-is-equivalence : adjunction-is-equivalence F⁻¹⊣F
  inverse-is-equivalence = record
    { unit-iso   = λ x → Cat.is-invertible-inverse D (counit-iso _)
    ; counit-iso = λ x → Cat.is-invertible-inverse C (unit-iso _)
    }
```
-->

Overloading terminology, a functor $F : \cC \to \cD$ is an **equivalence
of categories** when it is part of an adjoint equivalence $F \vdash G$.

```agda
record is-equivalence (F : Functor C D) : Type (adj-level C D) where
  field
    F⁻¹   : Functor D C
    F⊣F⁻¹ : F ⊣ F⁻¹

    has-is-equivalence : adjunction-is-equivalence F⊣F⁻¹

  open adjunction-is-equivalence has-is-equivalence public

  inverse-equivalence : is-equivalence F⁻¹
  inverse-equivalence = record
    { F⁻¹ = F
    ; F⊣F⁻¹ = F⁻¹⊣F
    ; has-is-equivalence = inverse-is-equivalence
    }
```

We chose, for definiteness, the above definition of equivalence of
categories, since it provides convenient access to the most useful data:
The induced natural isomorphisms, the adjunction unit/counit, and the
triangle identities. It _is_ a lot of data to come up with by hand,
though, so we provide some alternatives:

## Fully faithful, essentially surjective

Any [[fully faithful]] and [[(split!) essentially surjective|eso
functor]] functor determines an equivalence of precategories. Recall
that "split essentially surjective" means we have some determined
_procedure_ for picking out an essential fibre over any object $d :
\cD$: an object $F^*(d) : \cC$ together with a specified isomorphism
$F^*(d) \cong d$.

```agda
module _ {F : Functor C D} (ff : is-fully-faithful F) (eso : is-split-eso F) where
  import Cat.Reasoning C as C
  import Cat.Reasoning D as D
  private module di = D._≅_

  private
    ff⁻¹ : ∀ {x y} → D.Hom (F .F₀ x) (F .F₀ y) → C.Hom _ _
    ff⁻¹ = equiv→inverse ff
    module ff {x} {y} = Equiv (_ , ff {x} {y})
```

It remains to show that, when $F$ is fully faithful, this assignment of
essential fibres extends to a functor $\cD \to \cC$. For the
object part, we send $x$ to the specified preimage. For the morphism
part, the splitting gives us isomorphisms $F^*(x) \cong x$ and $F^*(y)
\cong y$, so that we may form the composite $F^*(x) \to x \to y \to
F^*(y)$; Fullness then completes the construction.

```agda
  ff+split-eso→inverse : Functor D C
  ff+split-eso→inverse .F₀ x         = eso x .fst
  ff+split-eso→inverse .F₁ {x} {y} f =
    ff⁻¹ (f*y-iso .D._≅_.from D.∘ f D.∘ f*x-iso .D._≅_.to)
    where
      open Σ (eso x) renaming (fst to f*x ; snd to f*x-iso)
      open Σ (eso y) renaming (fst to f*y ; snd to f*y-iso)
```

<details>
<summary>
We must then, as usual, prove that this definition preserves identities
and distributes over composites, so that we really have a functor.
Preservation of identities is immediate; Distribution over composites is
by faithfulness.
</summary>

```agda
  ff+split-eso→inverse .F-id {x} =
    ff⁻¹ (f*x-iso .di.from D.∘ ⌜ D.id D.∘ f*x-iso .di.to ⌝) ≡⟨ ap! (D.idl _) ⟩
    ff⁻¹ (f*x-iso .di.from D.∘ f*x-iso .di.to)              ≡⟨ ap ff⁻¹ (f*x-iso .di.invr) ⟩
    ff⁻¹ D.id                                               ≡˘⟨ ap ff⁻¹ (F .F-id) ⟩
    ff⁻¹ (F .F₁ C.id)                                       ≡⟨ ff.η _ ⟩
    C.id                                                    ∎
    where open Σ (eso x) renaming (fst to f*x ; snd to f*x-iso)

  ff+split-eso→inverse .F-∘ {x} {y} {z} f g =
    ff→faithful {F = F} ff (
      F .F₁ (ff⁻¹ (ffz D.∘ (f D.∘ g) D.∘ ftx))     ≡⟨ ff.ε _ ⟩
      ffz D.∘ (f D.∘ g) D.∘ ftx                    ≡⟨ cat! D ⟩
      ffz D.∘ f D.∘ ⌜ D.id ⌝ D.∘ g D.∘ ftx         ≡˘⟨ ap¡ (f*y-iso .di.invl) ⟩
      ffz D.∘ f D.∘ (fty D.∘ ffy) D.∘ g D.∘ ftx    ≡⟨ cat! D ⟩
      (ffz D.∘ f D.∘ fty) D.∘ (ffy D.∘ g D.∘ ftx)  ≡˘⟨ ap₂ D._∘_ (ff.ε _) (ff.ε _) ⟩
      F .F₁ (ff⁻¹ _) D.∘ F .F₁ (ff⁻¹ _)            ≡˘⟨ F .F-∘ _ _ ⟩
      F .F₁ (ff⁻¹ _ C.∘ ff⁻¹ _)                    ∎
    )
    where
      open Σ (eso x) renaming (fst to f*x ; snd to f*x-iso)
      open Σ (eso y) renaming (fst to f*y ; snd to f*y-iso)
      open Σ (eso z) renaming (fst to f*z ; snd to f*z-iso)

      ffz = f*z-iso .di.from
      ftz = f*z-iso .di.to
      ffy = f*y-iso .di.from
      fty = f*y-iso .di.to
      ffx = f*x-iso .di.from
      ftx = f*x-iso .di.to
```

</details>

We will, for brevity, refer to the functor we've just built as $G$,
rather than its "proper name" `ff+split-eso→inverse`{.Agda}. Hercules
now only has 11 labours to go: We must construct unit and counit natural
transformations, prove that they satisfy the triangle identities, and
prove that the unit/counit we define are componentwise invertible. I'll
keep the proofs of naturality in `<details>` tags since.. they're
_rough_.

```agda
  private
    G = ff+split-eso→inverse
```

For the unit, we have an object $x : \cC$ and we're asked to provide
a morphism $x \to F^*F(x)$ --- where, recall, the notation $F^*(x)$
represents the chosen essential fibre of $F$ over $x$. By fullness, it
suffices to provide a morphism $F(x) \to FF^*F(x)$; But recall that the
essential fibre $F^*F(x)$ comes equipped with an isomorphism $FF^*F(x)
\cong F(x)$.

```agda
  ff+split-eso→unit : Id => (G F∘ F)
  ff+split-eso→unit .η x = ff⁻¹ (f*x-iso .di.from)
    where open Σ (eso (F · x)) renaming (fst to f*x ; snd to f*x-iso)
```

<details>
<summary> Naturality of `ff+split-eso→unit`{.Agda}. </summary>

```agda
  ff+split-eso→unit .is-natural x y f =
    ff→faithful {F = F} ff (
      F .F₁ (ff⁻¹ ffy C.∘ f)                                      ≡⟨ F .F-∘ _ _ ⟩
      ⌜ F .F₁ (ff⁻¹ ffy) ⌝ D.∘ F .F₁ f                            ≡⟨ ap! (ff.ε _) ⟩
      ffy D.∘ ⌜ F .F₁ f ⌝                                         ≡⟨ ap! (sym (D.idr _) ∙ ap (F .F₁ f D.∘_) (sym (f*x-iso .di.invl))) ⟩
      ffy D.∘ F .F₁ f D.∘ ftx D.∘ ffx                             ≡⟨ cat! D ⟩
      (ffy D.∘ F .F₁ f D.∘ ftx) D.∘ ffx                           ≡˘⟨ ap₂ D._∘_ (ff.ε _) (ff.ε _) ⟩
      F .F₁ (ff⁻¹ (ffy D.∘ F .F₁ f D.∘ ftx)) D.∘ F .F₁ (ff⁻¹ ffx) ≡˘⟨ F .F-∘ _ _ ⟩
      F .F₁ (ff⁻¹ (ffy D.∘ F .F₁ f D.∘ ftx) C.∘ ff⁻¹ ffx)         ≡⟨⟩
      F .F₁ ((G F∘ F) .F₁ f C.∘ x→f*x)                            ∎
    )
    where
      open Σ (eso (F .F₀ x)) renaming (fst to f*x ; snd to f*x-iso)
      open Σ (eso (F .F₀ y)) renaming (fst to f*y ; snd to f*y-iso)

      ffy = f*y-iso .di.from
      fty = f*y-iso .di.to
      ffx = f*x-iso .di.from
      ftx = f*x-iso .di.to

      x→f*x : C.Hom x f*x
      x→f*x = ff⁻¹ (f*x-iso .di.from)

      y→f*y : C.Hom y f*y
      y→f*y = ff⁻¹ (f*y-iso .di.from)
```

</details>

For the counit, we have to provide a morphism $FF^*(x) \to x$; We can
again pick the given isomorphism.

```agda
  ff+split-eso→counit : (F F∘ G) => Id
  ff+split-eso→counit .η x = f*x-iso .di.to
    where open Σ (eso x) renaming (fst to f*x ; snd to f*x-iso)
```

<details>
<summary> Naturality of `ff+split-eso→counit`{.Agda} </summary>

```agda
  ff+split-eso→counit .is-natural x y f =
    fty D.∘ ⌜ F .F₁ (ff⁻¹ (ffy D.∘ f D.∘ ftx)) ⌝ ≡⟨ ap! (ff.ε _) ⟩
    fty D.∘ ffy D.∘ f D.∘ ftx                    ≡⟨ D.cancell (f*y-iso .di.invl) ⟩
    f D.∘ ftx                                    ∎
    where
      open Σ (eso x) renaming (fst to f*x ; snd to f*x-iso)
      open Σ (eso y) renaming (fst to f*y ; snd to f*y-iso)

      ffy = f*y-iso .di.from
      fty = f*y-iso .di.to
      ftx = f*x-iso .di.to
```

</details>

Checking the triangle identities, and that the adjunction unit/counit
defined above are natural isomorphisms, is routine. We present the
calculations without commentary:

```agda
  open _⊣_

  ff+split-eso→F⊣inverse : F ⊣ G
  ff+split-eso→F⊣inverse .unit    = ff+split-eso→unit
  ff+split-eso→F⊣inverse .counit  = ff+split-eso→counit
  ff+split-eso→F⊣inverse .zig {x} =
    ftx D.∘ F .F₁ (ff⁻¹ ffx) ≡⟨ ap (ftx D.∘_) (ff.ε _) ⟩
    ftx D.∘ ffx              ≡⟨ f*x-iso .di.invl ⟩
    D.id                     ∎
```
<!--
```agda
    where
      open Σ (eso (F .F₀ x)) renaming (fst to f*x ; snd to f*x-iso)

      ffx = f*x-iso .di.from
      ftx = f*x-iso .di.to
```
-->

The `zag`{.Agda} identity needs an appeal to faithfulness:

```agda
  ff+split-eso→F⊣inverse .zag {x} =
    ff→faithful {F = F} ff (
      F .F₁ (ff⁻¹ (ffx D.∘ ftx D.∘ fftx) C.∘ ff⁻¹ fffx)         ≡⟨ F .F-∘ _ _ ⟩
      F .F₁ (ff⁻¹ (ffx D.∘ ftx D.∘ fftx)) D.∘ F .F₁ (ff⁻¹ fffx) ≡⟨ ap₂ D._∘_ (ff.ε _) (ff.ε _) ⟩
      (ffx D.∘ ftx D.∘ fftx) D.∘ fffx                           ≡⟨ cat! D ⟩
      (ffx D.∘ ftx) D.∘ (fftx D.∘ fffx)                         ≡⟨ ap₂ D._∘_ (f*x-iso .di.invr) (f*f*x-iso .di.invl) ⟩
      D.id D.∘ D.id                                             ≡⟨ D.idl _ ∙ sym (F .F-id) ⟩
      F .F₁ C.id                                                ∎
    )
```

Now to show they are componentwise invertible:

<!--
```agda
    where
      open Σ (eso x) renaming (fst to f*x ; snd to f*x-iso)
      open Σ (eso (F .F₀ f*x)) renaming (fst to f*f*x ; snd to f*f*x-iso)

      ffx = f*x-iso .di.from
      ftx = f*x-iso .di.to
      fffx = f*f*x-iso .di.from
      fftx = f*f*x-iso .di.to
```
-->

```agda
  open adjunction-is-equivalence
  open is-equivalence

  ff+split-eso→is-equivalence : is-equivalence F
  ff+split-eso→is-equivalence .F⁻¹ = G
  ff+split-eso→is-equivalence .F⊣F⁻¹ = ff+split-eso→F⊣inverse
  ff+split-eso→is-equivalence .has-is-equivalence .counit-iso x = record
    { inv      = f*x-iso .di.from
    ; inverses = record
      { invl = f*x-iso .di.invl
      ; invr = f*x-iso .di.invr }
    }
    where open Σ (eso x) renaming (fst to f*x ; snd to f*x-iso)
```

Since the unit is defined in terms of fullness, showing it is invertible
needs an appeal to faithfulness (two, actually):

```agda
  ff+split-eso→is-equivalence .has-is-equivalence .unit-iso x = record
    { inv      = ff⁻¹ (f*x-iso .di.to)
    ; inverses = record
      { invl = ff→faithful {F = F} ff (
          F .F₁ (ff⁻¹ ffx C.∘ ff⁻¹ ftx)         ≡⟨ F .F-∘ _ _ ⟩
          F .F₁ (ff⁻¹ ffx) D.∘ F .F₁ (ff⁻¹ ftx) ≡⟨ ap₂ D._∘_ (ff.ε _) (ff.ε _) ⟩
          ffx D.∘ ftx                           ≡⟨ f*x-iso .di.invr ⟩
          D.id                                  ≡˘⟨ F .F-id ⟩
          F .F₁ C.id                            ∎)
      ; invr = ff→faithful {F = F} ff (
          F .F₁ (ff⁻¹ ftx C.∘ ff⁻¹ ffx)         ≡⟨ F .F-∘ _ _ ⟩
          F .F₁ (ff⁻¹ ftx) D.∘ F .F₁ (ff⁻¹ ffx) ≡⟨ ap₂ D._∘_ (ff.ε _) (ff.ε _) ⟩
          ftx D.∘ ffx                           ≡⟨ f*x-iso .di.invl ⟩
          D.id                                  ≡˘⟨ F .F-id ⟩
          F .F₁ C.id                            ∎)
      }
    }
    where
      open Σ (eso (F .F₀ x)) renaming (fst to f*x ; snd to f*x-iso)
      ffx = f*x-iso .di.from
      ftx = f*x-iso .di.to
```

### Between categories

Above, we made an equivalence out of any [[fully faithful]] and _split_
essentially surjective functor. In set-theoretic mathematics (and indeed
between [[strict categories]]), the splitting condition can not be
lifted constructively: the statement "every (ff, eso) functor between
strict categories is an equivalence" is equivalent to the axiom of
choice.

However, between [[univalent categories]], the situation is different: Any
essentially surjective [[fully faithful]] functor splits. In particular, any [[ff]] functor
between univalent categories has propositional [[essential fibres]], so a
"mere" essential surjection is automatically split. However, note that
_both_ the domain _and_ codomain have to be categories for the argument
to go through.

```agda
module
  _ (F : Functor C D) (ccat : is-category C) (dcat : is-category D)
    (ff : is-fully-faithful F)
  where
  private
    module D = Cat D using (cancell)
```

So, suppose we have categories $\cC$ and $\cD$, together with a
fully faithful functor $F : \cC \to \cD$. For any $y : \cD$,
we're given an inhabitant of $\| \sum_{x : \cC} F(x) \cong y \|$,
which we want to "get out" from under the truncation. For this, we'll
show that the type being truncated is a proposition, so that we may
"untruncate" it.

```agda
  Essential-fibre-between-cats-is-prop : ∀ y → is-prop (Essential-fibre F y)
  Essential-fibre-between-cats-is-prop z (x , i) (y , j) = they're-equal where
```

For this magic trick, assume we're given a $z : \cD$, together with
objects $x, y : \cC$ and isomorphisms $i : F(x) \cong z$ and $j :
F(y) \cong z$. We must show that $x \equiv y$, and that over this path,
$i = j$. Since $F$ is fully faithful, we can `find an isomorphism`{.Agda
ident=is-ff→essentially-injective} $x \cong y$ in $\cC$, which $F$
sends back to $i \circ j\inv$.

```agda
    Fx≅Fy : Cat.Isomorphism D (F · x) (F · y)
    Fx≅Fy = j Iso⁻¹ ∘Iso i

    x≅y : Cat.Isomorphism C x y
    x≅y = is-ff→essentially-injective {F = F} ff Fx≅Fy
```

Furthermore, since we're working with categories, these isomorphisms
restrict to _paths_ $x \equiv y$ and $F(x) \equiv F(y)$. We're
half-done: we've shown that some $p : x \equiv y$ exists, and it remains to
show that over this path we have $i \equiv j$. More specifically, we
must give a path $i \equiv j$ laying over $\ap{F}{p}$.

```agda
    x≡y : x ≡ y
    x≡y = ccat .to-path x≅y

    Fx≡Fy : F .F₀ x ≡ F .F₀ y
    Fx≡Fy = dcat .to-path Fx≅Fy
```

Rather than showing it over $p : x\equiv y$ directly, we'll show it over
the path $F(x) \equiv F(y)$ we constructed independently. This is
because we can use the helper `Hom-pathp-reflr-iso`{.Agda} to establish
the result with far less computation:

```agda
    over' : PathP (λ i → Cat.Isomorphism D (Fx≡Fy i) z) i j
    over' = Cat.≅-pathp _ Fx≡Fy refl
      (Univalent.Hom-pathp-refll-iso dcat (D.cancell (i .invl)))
```

We must then connect $\ap{F}{p}$ with this path $F(x) \cong F(y)$. But
since we originally got $p$ by full faithfulness of $F$, they _are_
indeed the same path:

```agda
    abstract
      square : ap· F x≡y ≡ Fx≡Fy
      square =
        ap· F x≡y                         ≡⟨ F-map-path F ccat dcat x≅y ⟩
        dcat .to-path ⌜ F-map-iso F x≅y ⌝ ≡⟨ ap! (equiv→counit (is-ff→F-map-iso-is-equiv {F = F} ff) _)  ⟩
        dcat .to-path Fx≅Fy               ∎

    over : PathP (λ i → Cat.Isomorphism D (F · x≡y i) z) i j
    over = transport (λ l → PathP (λ m → Cat.Isomorphism D (square (~ l) m) z) i j) over'
```

Hence --- blink and you'll miss it --- the essential fibres of $F$ over
any $z : \cD$ are propositions, so it suffices for them to be merely
inhabited for the functor to be split eso. With tongue firmly in cheek
we call this result the _theorem of choice_.

```agda
    they're-equal = Σ-pathp x≡y over

  Theorem-of-choice : is-eso F → is-split-eso F
  Theorem-of-choice eso y =
    ∥-∥-elim (λ _ → Essential-fibre-between-cats-is-prop y)
      (λ x → x) (eso y)
```

This theorem implies that any fully faithful, "merely" essentially
surjective functor between categories is an equivalence:

```agda
  ff+eso→is-equivalence : is-eso F → is-equivalence F
  ff+eso→is-equivalence eso = ff+split-eso→is-equivalence ff (Theorem-of-choice eso)
```

Furthermore, if $F : \cC \to \cD$ is an equivalence between categories,
then it's an equivalence-on-objects functor. The inverse functor
$F\inv : \cD \to \cC$ gives us a way to turn objects of $\cD$ back
into objects of $\cC$, and unit/counit of the equivalence ensure
that $c \cong F\inv(F(c))$ and $d \cong F(F\inv(d))$, so all that remains
is to use the fact that $\cC$ and $\cD$ are categories to get the
requisite paths.

```agda
is-cat-equivalence→equiv-on-objects
  : ∀ {F : Functor C D}
  → (ccat : is-category C) (dcat : is-category D)
  → is-equivalence F → is-equiv-on-objects F
is-cat-equivalence→equiv-on-objects {C = C} {D = D} {F = F} ccat dcat eqv =
  is-iso→is-equiv $
    iso (e.F⁻¹ .F₀)
      (λ d → dcat .to-path (Cat.invertible→iso _ _ (e.counit-iso d)))
      (λ c → sym $ ccat .to-path (Cat.invertible→iso _ _ (e.unit-iso c)))
  where
    module e = is-equivalence eqv
```

## Isomorphisms {defines="isomorphism-of-precategories"}

Another, more direct way of proving that a functor is an equivalence of
precategories is proving that it is an **isomorphism of precategories**:
It's fully faithful, thus a typal equivalence of morphisms, and in
addition its action on objects is an equivalence of types.

```agda
record is-precat-iso (F : Functor C D) : Type (adj-level C D) where
  no-eta-equality
  constructor iso
  field
    has-is-ff  : is-fully-faithful F
    has-is-iso : is-equiv (F .F₀)
```

Such a functor is (immediately) fully faithful, and the inverse
`has-is-iso`{.Agda} means that it is split essentially surjective; For
given $y : D$, the inverse of $F_0$ gives us an object $F\inv(y)$; We must
then provide an isomorphism $F(F\inv(y)) \cong y$, but those are
identical, hence isomorphic.

```agda
module _ {F : Functor C D} (p : is-precat-iso F) where
  open is-precat-iso p

  is-precat-iso→is-split-eso : is-split-eso F
  is-precat-iso→is-split-eso ob = equiv→inverse has-is-iso ob , isom
    where isom = path→iso {C = D} (equiv→counit has-is-iso _)
```

Thus, by the theorem above, $F$ is an adjoint equivalence of
precategories.

```agda
  is-precat-iso→is-equivalence : is-equivalence F
  is-precat-iso→is-equivalence =
    ff+split-eso→is-equivalence has-is-ff is-precat-iso→is-split-eso
```

<!--
```agda
open adjunction-is-equivalence
open is-equivalence
open Precategory
open _⊣_

unquoteDecl H-Level-is-precat-iso = declare-record-hlevel 1 H-Level-is-precat-iso (quote is-precat-iso)

module
  _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
    (F : Functor C D) (eqv : is-equivalence F)
  where
  private
    module e = is-equivalence eqv
    module C = Cat C using (_∘_ ; cancell)
    module D = Cat D using (invertible→monic ; cancell ; _∘_)
    module F = Fr F

  is-equivalence→is-ff : is-fully-faithful F
  is-equivalence→is-ff = is-iso→is-equiv λ where
    .is-iso.from x → e.unit⁻¹ .η _ C.∘ L-adjunct e.F⊣F⁻¹ x
    .is-iso.rinv x →
      D.invertible→monic (F-map-invertible F (e.unit-iso _)) _ _ $
        ap₂ D._∘_ refl (F .F-∘ _ _)
      ∙∙ D.cancell (F.annihilate (e.unit-iso _ .invl))
      ∙∙ D.invertible→monic (e.counit-iso _) _ _
          (R-L-adjunct e.F⊣F⁻¹ x ∙ sym (D.cancell e.zig))
    .is-iso.linv x →
        ap (_ C.∘_) (sym (e.unit .is-natural _ _ _))
      ∙ C.cancell (e.unit-iso _ .invr)

  is-equivalence→is-split-eso : is-split-eso F
  is-equivalence→is-split-eso y =
    (e.F⁻¹ .F₀ y) ,
    Cat.invertible→iso D (e.counit .η y) (e.counit-iso y)

  is-equivalence→is-eso : is-eso F
  is-equivalence→is-eso y =
    inc ((e.F⁻¹ .F₀ y) , Cat.invertible→iso D (e.counit .η y) (e.counit-iso y))

  open is-precat-iso
  open is-iso

  is-equivalence→is-precat-iso
    : is-category C → is-category D → is-precat-iso F
  is-equivalence→is-precat-iso c-cat d-cat .has-is-ff =
    is-equivalence→is-ff
  is-equivalence→is-precat-iso c-cat d-cat .has-is-iso =
    is-cat-equivalence→equiv-on-objects c-cat d-cat eqv
```
-->

<!--
```agda
record Equivalence
  {o ℓ o' ℓ'} (C : Precategory o ℓ) (D : Precategory o' ℓ')
  : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ')
  where
  no-eta-equality
  field
    To : Functor C D
    To-equiv : is-equivalence To

  open is-equivalence To-equiv renaming (F⁻¹ to From; F⊣F⁻¹ to To⊣From) public
```
-->

## Properties of equivalences

If $F : \cC \to \cD$ is fully-faithfuly and essentially surjective, then
for every hom-set $\cD(d,d')$ there (merely) exists an equivalent hom-set
$\cC(c,c')$.

<!--
```agda
module _
  {oc ℓc od ℓd}
  {C : Precategory oc ℓc}
  {D : Precategory od ℓd}
  where
  private
    module C = Precategory C using (Hom)
    module D = Precategory D using (Hom)
```
-->

```agda
  ff+split-eso→hom-equiv
    : (F : Functor C D)
    → is-fully-faithful F
    → is-split-eso F
    → ∀ d d' → Σ[ c ∈ C ] Σ[ c' ∈ C ] (C.Hom c c' ≃ D.Hom d d')
  ff+split-eso→hom-equiv F ff split-eso d d' =
    d-fib .fst , d'-fib .fst ,
    (F .F₁ , ff) ∙e Cat.iso→hom-equiv D (d-fib .snd) (d'-fib .snd)
    where
      d-fib = split-eso d
      d'-fib = split-eso d'

  ff+eso→hom-equiv
    : (F : Functor C D)
    → is-fully-faithful F
    → is-eso F
    → ∀ d d' → ∃[ c ∈ C ] Σ[ c' ∈ C ] (C.Hom c c' ≃ D.Hom d d')
  ff+eso→hom-equiv F ff eso d d' = do
      (c , Fc≅d) ← eso d
      (c' , Fc'≅d') ← eso d'
      pure (c , c' , (F .F₁ , ff) ∙e Cat.iso→hom-equiv D Fc≅d Fc'≅d')
```

This allows us to prove a very useful little lemma: if $F : \cC \to \cD$ is a
fully-faithful, essentially surjective functor, then any property of hom-sets
of $\cC$ that holds for all hom-sets must also hold for all hom-sets of $\cD$.

```agda
  ff+eso→preserves-hom-props
    : ∀ {ℓ} (F : Functor C D)
    → is-fully-faithful F
    → is-eso F
    → (P : Type (ℓc ⊔ ℓd) → Type ℓ)
    → (∀ A → is-prop (P A))
    → (∀ c c' → P (Lift ℓd (C.Hom c c')))
    → ∀ d d' → P (Lift ℓc (D.Hom d d'))
  ff+eso→preserves-hom-props F ff eso P prop P-hom d d' =
    ∥-∥-out (prop (Lift ℓc (D.Hom d d'))) $ do
      (c , c' , eqv) ← ff+eso→hom-equiv F ff eso d d'
      pure (transport (ap P (ua (Lift-ap eqv))) (P-hom c c'))
```

As a corollary, we note that if $F : \cC \to \cD$ is a fully-faithful, essentially
surjective functor, then if the hom-sets of $\cC$ are all $n$-types, then the hom-sets
of $\cD$ must also be $n$-types.

```agda
  ff+eso→hom-hlevel
    : ∀ {n} (F : Functor C D)
    → is-fully-faithful F
    → is-eso F
    → (∀ c c' → is-hlevel (C.Hom c c') n)
    → ∀ d d' → is-hlevel (D.Hom d d') n
  ff+eso→hom-hlevel {n = n} F ff eso C-hlevel d d' =
    Lift-is-hlevel' _ $
    ff+eso→preserves-hom-props F ff eso
      (λ A → is-hlevel A n) (λ _ → is-hlevel-is-prop n)
      (λ c c' → Lift-is-hlevel n (C-hlevel c c')) d d'
```

Note that if $F$ is fully faithful and **split** essentially surjective, then
we can drop the requirement that $P$ must be a prop.

```agda
  ff+split-eso→preserves-hom-fams
    : ∀ {ℓ} (F : Functor C D)
    → is-fully-faithful F
    → is-split-eso F
    → (P : Type (ℓc ⊔ ℓd) → Type ℓ)
    → (∀ c c' → P (Lift ℓd (C.Hom c c')))
    → ∀ d d' → P (Lift ℓc (D.Hom d d'))
  ff+split-eso→preserves-hom-fams F ff split-eso P P-hom d d' =
    transport
      (ap P (ua (Lift-ap (ff+split-eso→hom-equiv F ff split-eso d d' .snd .snd))))
      (P-hom _ _)
```

As a corollary, equivalences preserve all families over hom sets.

```agda
  equivalence→preserves-hom-fams
    : ∀ {ℓ} (E : Equivalence C D)
    → (P : Type (ℓc ⊔ ℓd) → Type ℓ)
    → (∀ c c' → P (Lift ℓd (C.Hom c c')))
    → ∀ d d' → P (Lift ℓc (D.Hom d d'))
  equivalence→preserves-hom-fams E =
    ff+split-eso→preserves-hom-fams (Equivalence.To E)
      (is-equivalence→is-ff _ (Equivalence.To-equiv E))
      (is-equivalence→is-split-eso _ (Equivalence.To-equiv E))
```

<!--
```agda
  equivalence→hom-hlevel
    : ∀ {n} (E : Equivalence C D)
    → (∀ c c' → is-hlevel (C.Hom c c') n)
    → ∀ d d' → is-hlevel (D.Hom d d') n
  equivalence→hom-hlevel {n = n} E C-hlevel d d' =
    Lift-is-hlevel' n $
    equivalence→preserves-hom-fams E (λ A → is-hlevel A n)
      (λ c c' → Lift-is-hlevel n (C-hlevel c c')) d d'
```
-->

Being an equivalence is also invariant under natural isomorphism.

```agda
is-equivalence-natural-iso
  : ∀ {F G : Functor C D}
  → F ≅ⁿ G
  → is-equivalence F → is-equivalence G
is-equivalence-natural-iso {C = C} {D = D} {F = F} {G = G} α F-eqv = G-eqv where
  open is-equivalence
  module C = Cat C using (invertible-∘ ; id-invertible)
  module D = Cat D using (invertible-∘ ; _invertible⁻¹)

  G-eqv : is-equivalence G
  G-eqv .F⁻¹ = F-eqv .F⁻¹
  G-eqv .F⊣F⁻¹ = adjoint-natural-isol α (F-eqv .F⊣F⁻¹)
  G-eqv .has-is-equivalence .unit-iso x = C.invertible-∘
    (C.invertible-∘
      C.id-invertible
      (F-map-invertible (F-eqv .F⁻¹) (isoⁿ→is-invertible α x)))
    (F-eqv .unit-iso x)
  G-eqv .has-is-equivalence .counit-iso x = D.invertible-∘ (F-eqv .counit-iso x)
    (D.invertible-∘
      (isoⁿ→is-invertible α _ D.invertible⁻¹)
      (F-map-invertible G C.id-invertible))
```

Equivalences are invertible.

```agda
_Equivalence⁻¹
  : Equivalence C D → Equivalence D C
(E Equivalence⁻¹) .Equivalence.To = Equivalence.From E
(E Equivalence⁻¹) .Equivalence.To-equiv = Equivalence.inverse-equivalence E
```

Equivalences are also composable, as [adjoints compose].

[adjoints compose]: Cat.Functor.Adjoint.Compose.html

```agda
is-equivalence-∘
  : ∀ {F : Functor D E} {G : Functor C D}
  → is-equivalence F → is-equivalence G
  → is-equivalence (F F∘ G)
is-equivalence-∘ {E = E} {C = C}  {F = F} {G = G} F-eqv G-eqv = FG-eqv where
  module F-eqv = is-equivalence F-eqv
  module G-eqv = is-equivalence G-eqv
  module C = Cat C using (invertible-∘)
  module E = Cat E using (invertible-∘)

  FG-eqv : is-equivalence (F F∘ G)
  FG-eqv .F⁻¹ = G-eqv.F⁻¹ F∘ F-eqv.F⁻¹
  FG-eqv .F⊣F⁻¹ = G-eqv.F⊣F⁻¹ ∘⊣ F-eqv.F⊣F⁻¹
  FG-eqv .has-is-equivalence .unit-iso x =
    C.invertible-∘
      (F-map-invertible G-eqv.F⁻¹ (F-eqv.unit-iso (G .F₀ x)))
      (G-eqv.unit-iso x)
  FG-eqv .has-is-equivalence .counit-iso x =
    E.invertible-∘
      (F-eqv.counit-iso x)
      (F-map-invertible F (G-eqv.counit-iso (F-eqv .F⁻¹ .F₀ x)))

_∘Equivalence_ : Equivalence C D → Equivalence D E → Equivalence C E
(F ∘Equivalence G) .Equivalence.To =
  Equivalence.To G F∘ Equivalence.To F
(F ∘Equivalence G) .Equivalence.To-equiv =
  is-equivalence-∘ (Equivalence.To-equiv G) (Equivalence.To-equiv F)
```

Unsurprisingly, the identity functor is an equivalence.

```agda
Id-is-equivalence : ∀ {o h} {C : Precategory o h} → is-equivalence {C = C} Id
Id-is-equivalence {C = C} .F⁻¹ = Id
Id-is-equivalence {C = C} .F⊣F⁻¹ .unit .η x = C .id
Id-is-equivalence {C = C} .F⊣F⁻¹ .unit .is-natural x y f = C .idl _ ∙ sym (C .idr _)
Id-is-equivalence {C = C} .F⊣F⁻¹ .counit .η x = C .id
Id-is-equivalence {C = C} .F⊣F⁻¹ .counit .is-natural x y f = C .idl _ ∙ sym (C .idr _)
Id-is-equivalence {C = C} .F⊣F⁻¹ .zig = C .idl _
Id-is-equivalence {C = C} .F⊣F⁻¹ .zag = C .idl _
Id-is-equivalence {C = C} .has-is-equivalence .unit-iso x =
  Cat.make-invertible C (C .id) (C .idl _) (C .idl _)
Id-is-equivalence {C = C} .has-is-equivalence .counit-iso x =
  Cat.make-invertible C (C .id) (C .idl _) (C .idl _)
```

### Preserving invertibility

We can characterise equivalences as those adjunctions $L \dashv R$ that
*preserve invertibility*, in the sense that the adjunct of an isomorphism
$L(a) \cong b$ is an isomorphism $a \cong R(b)$ and vice versa;
that is, the property of being invertible in $\cC$ is equivalent to
the property of being invertible in $\cD$ [[over|equivalence over]]
the adjunction's $\hom$-equivalence $(L(a) \to b) \simeq (a \to R(b))$.

<!--
```agda
module
  _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
    {L : Functor C D} {R : Functor D C} (L⊣R : L ⊣ R)
  where
  private
    module C = Cat C using (is-invertible ; invertible-cancelr ; id ; id-invertible)
    module D = Cat D using (is-invertible ; invertible-cancell ; id ; id-invertible)
    module L = Fr L
    module R = Fr R
```
-->

```agda
  preserves-invertibility : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ')
  preserves-invertibility = ∀ {a b} →
    D.is-invertible ≃[ adjunct-hom-equiv L⊣R {a} {b} ] C.is-invertible
```

Since the unit and counit of an adjunction are adjuncts of identities,
it's not hard to see that they must be invertible if the adjunction
preserves invertibility.

```agda
  preserves-invertibility→equivalence
    : preserves-invertibility → is-equivalence L
  preserves-invertibility→equivalence e .F⁻¹ = R
  preserves-invertibility→equivalence e .F⊣F⁻¹ = L⊣R
  preserves-invertibility→equivalence e .has-is-equivalence .unit-iso c =
    C.invertible-cancelr
      (R.F-map-invertible D.id-invertible)
      (Equiv.to (e D.id _ refl) D.id-invertible)
  preserves-invertibility→equivalence e .has-is-equivalence .counit-iso d =
    D.invertible-cancell
      (L.F-map-invertible C.id-invertible)
      (Equiv.from (e _ _ (L-R-adjunct L⊣R _)) C.id-invertible)
```

The other direction is just as straightforward, since adjuncts are
defined by composition with the (co)unit, and isomorphisms compose.

<!--
```agda
module
  _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
    (F : Functor C D) (eqv : is-equivalence F)
  where
  private
    module e = is-equivalence eqv
    module F = Fr F
    module F⁻¹ = Fr e.F⁻¹
```
-->

```agda
  equivalence→preserves-invertibility : preserves-invertibility e.F⊣F⁻¹
  equivalence→preserves-invertibility = prop-over-ext
    (adjunct-hom-equiv e.F⊣F⁻¹)
    (hlevel 1) (hlevel 1)
    (λ f inv → Cat.invertible-∘ _ (F⁻¹.F-map-invertible inv) (e.unit-iso _))
    (λ f inv → Cat.invertible-∘ _ (e.counit-iso _) (F.F-map-invertible inv))
```
