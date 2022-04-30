```agda
open import Cat.Instances.Functor
open import Cat.Functor.Adjoint
open import Cat.Functor.Base
open import Cat.Univalent
open import Cat.Prelude

import Cat.Reasoning

module Cat.Functor.Equivalence where
```

<!--
```agda
private variable
  o h : Level
  C D : Precategory o h
open Functor hiding (op)
open _=>_ hiding (op)
```
-->

# Equivalences

A functor $F : \ca{C} \to \ca{D}$ is an **equivalence of categories**
when it has a [right adjoint] $G : \ca{D} \to \ca{D}$, with the unit and
counit natural transformations being [natural isomorphisms]. This
immediately implies that our adjoint pair $F \dashv G$ extends to an
adjoint triple $F \dashv G \dashv F$.

[right adjoint]: Cat.Functor.Adjoint.html
[natural isomorphisms]: Cat.Instances.Functor.html#functor-categories

```agda
record is-equivalence (F : Functor C D) : Type (adj-level C D) where
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module [C,C] = Cat.Reasoning Cat[ C , C ]
    module [D,D] = Cat.Reasoning Cat[ D , D ]

  field
    F⁻¹      : Functor D C
    F⊣F⁻¹    : F ⊣ F⁻¹

  open _⊣_ F⊣F⁻¹ public

  field
    unit-iso   : ∀ x → C.is-invertible (unit.η x)
    counit-iso : ∀ x → D.is-invertible (counit.ε x)
```

The first thing we note is that having a natural family of invertible
morphisms gives isomorphisms in the respective functor categories:

```agda
  F∘F⁻¹≅Id : (F F∘ F⁻¹) [D,D].≅ Id
  F∘F⁻¹≅Id =
    [D,D].invertible→iso counit
      (componentwise-invertible→invertible _ counit-iso)

  Id≅F⁻¹∘F : Id [C,C].≅ (F⁻¹ F∘ F)
  Id≅F⁻¹∘F =
    [C,C].invertible→iso unit
      (componentwise-invertible→invertible _ unit-iso)

  unit⁻¹ = [C,C]._≅_.from Id≅F⁻¹∘F
  counit⁻¹ = [D,D]._≅_.from F∘F⁻¹≅Id
```

<!--
```agda
  F⁻¹⊣F : F⁻¹ ⊣ F
  F⁻¹⊣F = adj′ where
    module adj = _⊣_ F⊣F⁻¹
    open _⊣_
    adj′ : F⁻¹ ⊣ F
    adj′ .unit   = counit⁻¹
    adj′ .counit = unit⁻¹
    adj′ .zig {a} = zig′ where abstract
      p : η unit⁻¹ (F₀ F⁻¹ a) ≡ F₁ F⁻¹ (adj.counit.ε _)
      p =
        η unit⁻¹ (F₀ F⁻¹ a)                                                ≡⟨ C.introl adj.zag ⟩
        (F₁ F⁻¹ (adj.counit.ε _) C.∘ adj.unit.η _) C.∘ η unit⁻¹ (F₀ F⁻¹ a) ≡⟨ C.cancelr (unit-iso _ .C.is-invertible.invl) ⟩
        F₁ F⁻¹ (adj.counit.ε _)                                            ∎

      zig′ : η unit⁻¹ (F₀ F⁻¹ a) C.∘ F⁻¹ .F₁ (counit⁻¹ .η a) ≡ C.id
      zig′ = ap₂ C._∘_ p refl
        ·· sym (F-∘ F⁻¹ _ _)
        ·· ap (F₁ F⁻¹) (counit-iso _ .D.is-invertible.invl) ∙ F-id F⁻¹

    adj′ .zag {b} = zag′ where abstract
      p : counit⁻¹ .η (F₀ F b) ≡ F .F₁ (adj.unit.η b)
      p =
        counit⁻¹ .η _                                                     ≡⟨ D.intror adj.zig ⟩
        counit⁻¹ .η _ D.∘ adj.counit.ε (F₀ F b) D.∘ (F₁ F (adj.unit.η b)) ≡⟨ D.cancell (counit-iso _ .D.is-invertible.invr) ⟩
        F .F₁ (adj.unit.η b)                                              ∎

      zag′ : F .F₁ (unit⁻¹ .η b) D.∘ counit⁻¹ .η (F₀ F b) ≡ D.id
      zag′ = ap₂ D._∘_ refl p
        ·· sym (F .F-∘ _ _)
        ·· (ap (F .F₁) (unit-iso _ .C.is-invertible.invr) ∙ F .F-id)

  inverse-equivalence : is-equivalence F⁻¹
  inverse-equivalence =
    record { F⁻¹ = F ; F⊣F⁻¹ = F⁻¹⊣F
           ; unit-iso   = λ x → D.is-invertible-inverse (counit-iso _)
           ; counit-iso = λ x → C.is-invertible-inverse (unit-iso _)
           }
```
-->

We chose, for definiteness, the above definition of equivalence of
categories, since it provides convenient access to the most useful data:
The induced natural isomorphisms, the adjunction unit/counit, and the
triangle identities. It _is_ a lot of data to come up with by hand,
though, so we provide some alternatives:

## Fully faithful, essentially surjective

Any [fully faithful][ff] and [(split!) essentially surjective][eso]
functor determines an equivalence of precategories. Recall that "split
essentially surjective" means we have some determined _procedure_ for
picking out an essential fibre over any object $d : \ca{D}$: an object
$F^*(d) : \ca{C}$ together with a specified isomorphism $F^*(d) \cong
d$.

[ff]: Cat.Functor.Base.html#ff-functors
[eso]: Cat.Functor.Base.html#essential-fibres

```agda
module _ {F : Functor C D} (ff : is-fully-faithful F) (eso : is-split-eso F) where
  import Cat.Reasoning C as C
  import Cat.Reasoning D as D
  private module di = D._≅_

  private
    ff⁻¹ : ∀ {x y} → D.Hom (F .F₀ x) (F .F₀ y) → C.Hom _ _
    ff⁻¹ = equiv→inverse ff
```

It remains to show that, when $F$ is fully faithful, this assignment of
essential fibres extends to a functor $\ca{D} \to \ca{C}$. For the
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
      open ∑ (eso x) renaming (fst to f*x ; snd to f*x-iso)
      open ∑ (eso y) renaming (fst to f*y ; snd to f*y-iso)
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
    ff⁻¹ (f*x-iso .di.from D.∘ D.id D.∘ f*x-iso .di.to) ≡⟨ ap ff⁻¹ (ap₂ D._∘_ refl (D.idl _)) ⟩
    ff⁻¹ (f*x-iso .di.from D.∘ f*x-iso .di.to)          ≡⟨ ap ff⁻¹ (f*x-iso .di.invr) ⟩
    ff⁻¹ D.id                                           ≡˘⟨ ap ff⁻¹ (F-id F) ⟩
    ff⁻¹ (F₁ F C.id)                                    ≡⟨ equiv→retraction ff _ ⟩
    C.id ∎
    where open ∑ (eso x) renaming (fst to f*x ; snd to f*x-iso)

  ff+split-eso→inverse .F-∘ {x} {y} {z} f g =
    fully-faithful→faithful {F = F} ff (
      F₁ F (ff⁻¹ (ffz D.∘ (f D.∘ g) D.∘ ftx))      ≡⟨ equiv→section ff _ ⟩
      ffz D.∘ (f D.∘ g) D.∘ ftx                    ≡⟨ solve D ⟩
      ffz D.∘ f D.∘ D.id D.∘ g D.∘ ftx             ≡˘⟨ ap (λ x → ffz D.∘ (f D.∘ (x D.∘ (g D.∘ ftx)))) (f*y-iso .di.invl) ⟩
      ffz D.∘ f D.∘ (fty D.∘ ffy) D.∘ g D.∘ ftx    ≡⟨ solve D ⟩
      (ffz D.∘ f D.∘ fty) D.∘ (ffy D.∘ g D.∘ ftx)  ≡˘⟨ ap₂ D._∘_ (equiv→section ff _) (equiv→section ff _) ⟩
      F₁ F (ff⁻¹ _) D.∘ F₁ F (ff⁻¹ _)              ≡˘⟨ F-∘ F _ _ ⟩
      F₁ F (ff⁻¹ _ C.∘ ff⁻¹ _)                     ∎
    )
    where
      open ∑ (eso x) renaming (fst to f*x ; snd to f*x-iso)
      open ∑ (eso y) renaming (fst to f*y ; snd to f*y-iso)
      open ∑ (eso z) renaming (fst to f*z ; snd to f*z-iso)

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

For the unit, we have an object $x : \ca{C}$ and we're asked to provide
a morphism $x \to F^*F(x)$ --- where, recall, the notation $F^*(x)$
represents the chosen essential fibre of $F$ over $x$. By fullness, it
suffices to provide a morphism $F(x) \to FF^*F(x)$; But recall that the
essential fibre $F^*F(x)$ comes equipped with an isomorphism $FF^*F(x)
\cong F(x)$.

```agda
  ff+split-eso→unit : Id => (G F∘ F)
  ff+split-eso→unit .η x = ff⁻¹ (f*x-iso .di.from)
    where open ∑ (eso (F₀ F x)) renaming (fst to f*x ; snd to f*x-iso)
```

<details>
<summary> Naturality of `ff+split-eso→unit`{.Agda}. </summary>

```agda
  ff+split-eso→unit .is-natural x y f =
    fully-faithful→faithful {F = F} ff (
      F₁ F (ff⁻¹ ffy C.∘ f)                                    ≡⟨ F-∘ F _ _ ⟩
      F₁ F (ff⁻¹ ffy) D.∘ F₁ F f                               ≡⟨ ap₂ D._∘_ (equiv→section ff _) refl ⟩
      ffy D.∘ F₁ F f                                           ≡⟨ ap₂ D._∘_ refl (sym (D.idr _) ∙ ap (F₁ F f D.∘_) (sym (f*x-iso .di.invl))) ⟩
      ffy D.∘ F₁ F f D.∘ ftx D.∘ ffx                           ≡⟨ solve D ⟩
      (ffy D.∘ F₁ F f D.∘ ftx) D.∘ ffx                         ≡˘⟨ ap₂ D._∘_ (equiv→section ff _) (equiv→section ff _) ⟩
      F₁ F (ff⁻¹ (ffy D.∘ F₁ F f D.∘ ftx)) D.∘ F₁ F (ff⁻¹ ffx) ≡˘⟨ F-∘ F _ _ ⟩
      F₁ F (ff⁻¹ (ffy D.∘ F₁ F f D.∘ ftx) C.∘ ff⁻¹ ffx)        ≡⟨⟩
      F₁ F (F₁ (G F∘ F) f C.∘ x→f*x)                           ∎
    )
    where
      open ∑ (eso (F₀ F x)) renaming (fst to f*x ; snd to f*x-iso)
      open ∑ (eso (F₀ F y)) renaming (fst to f*y ; snd to f*y-iso)

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
    where open ∑ (eso x) renaming (fst to f*x ; snd to f*x-iso)
```

<details>
<summary> Naturality of `ff+split-eso→counit`{.Agda} </summary>

```agda
  ff+split-eso→counit .is-natural x y f =
    fty D.∘ F₁ F (ff⁻¹ (ffy D.∘ f D.∘ ftx)) ≡⟨ ap (fty D.∘_) (equiv→section ff _) ⟩
    fty D.∘ ffy D.∘ f D.∘ ftx               ≡⟨ D.cancell (f*y-iso .di.invl) ⟩
    f D.∘ ftx                               ∎
    where
      open ∑ (eso x) renaming (fst to f*x ; snd to f*x-iso)
      open ∑ (eso y) renaming (fst to f*y ; snd to f*y-iso)

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
    ftx D.∘ F₁ F (ff⁻¹ ffx) ≡⟨ ap (ftx D.∘_) (equiv→section ff _) ⟩
    ftx D.∘ ffx             ≡⟨ f*x-iso .di.invl ⟩
    D.id                    ∎
```
<!--
```agda
    where
      open ∑ (eso (F₀ F x)) renaming (fst to f*x ; snd to f*x-iso)

      ffx = f*x-iso .di.from
      ftx = f*x-iso .di.to
```
-->

The `zag`{.Agda} identity needs an appeal to faithfulness:

```agda
  ff+split-eso→F⊣inverse .zag {x} =
    fully-faithful→faithful {F = F} ff (
      F₁ F (ff⁻¹ (ffx D.∘ ftx D.∘ fftx) C.∘ ff⁻¹ fffx)        ≡⟨ F-∘ F _ _ ⟩
      F₁ F (ff⁻¹ (ffx D.∘ ftx D.∘ fftx)) D.∘ F₁ F (ff⁻¹ fffx) ≡⟨ ap₂ D._∘_ (equiv→section ff _) (equiv→section ff _) ⟩
      (ffx D.∘ ftx D.∘ fftx) D.∘ fffx                         ≡⟨ solve D ⟩
      (ffx D.∘ ftx) D.∘ (fftx D.∘ fffx)                       ≡⟨ ap₂ D._∘_ (f*x-iso .di.invr) (f*f*x-iso .di.invl) ⟩
      D.id D.∘ D.id                                           ≡⟨ D.idl _ ∙ sym (F-id F) ⟩
      F₁ F C.id                                               ∎
    )
```

Now to show they are componentwise invertible:

<!--
```agda
    where
      open ∑ (eso x) renaming (fst to f*x ; snd to f*x-iso)
      open ∑ (eso (F₀ F f*x)) renaming (fst to f*f*x ; snd to f*f*x-iso)

      ffx = f*x-iso .di.from
      ftx = f*x-iso .di.to
      fffx = f*f*x-iso .di.from
      fftx = f*f*x-iso .di.to
```
-->

```agda
  open is-equivalence

  ff+split-eso→is-equivalence : is-equivalence F
  ff+split-eso→is-equivalence .F⁻¹ = G
  ff+split-eso→is-equivalence .F⊣F⁻¹ = ff+split-eso→F⊣inverse
  ff+split-eso→is-equivalence .counit-iso x = record
    { inv      = f*x-iso .di.from
    ; inverses = record
      { invl = f*x-iso .di.invl
      ; invr = f*x-iso .di.invr }
    }
    where open ∑ (eso x) renaming (fst to f*x ; snd to f*x-iso)
```

Since the unit is defined in terms of fullness, showing it is invertible
needs an appeal to faithfulness (two, actually):

```agda
  ff+split-eso→is-equivalence .unit-iso x = record
    { inv      = ff⁻¹ (f*x-iso .di.to)
    ; inverses = record
      { invl = fully-faithful→faithful {F = F} ff (
          F₁ F (ff⁻¹ ffx C.∘ ff⁻¹ ftx)        ≡⟨ F-∘ F _ _ ⟩
          F₁ F (ff⁻¹ ffx) D.∘ F₁ F (ff⁻¹ ftx) ≡⟨ ap₂ D._∘_ (equiv→section ff _) (equiv→section ff _) ⟩
          ffx D.∘ ftx                         ≡⟨ f*x-iso .di.invr ⟩
          D.id                                ≡˘⟨ F-id F ⟩
          F₁ F C.id                           ∎)
      ; invr = fully-faithful→faithful {F = F} ff (
          F₁ F (ff⁻¹ ftx C.∘ ff⁻¹ ffx)        ≡⟨ F-∘ F _ _ ⟩
          F₁ F (ff⁻¹ ftx) D.∘ F₁ F (ff⁻¹ ffx) ≡⟨ ap₂ D._∘_ (equiv→section ff _) (equiv→section ff _) ⟩
          ftx D.∘ ffx                         ≡⟨ f*x-iso .di.invl ⟩
          D.id                                ≡˘⟨ F-id F ⟩
          F₁ F C.id                           ∎)
      }
    }
    where
      open ∑ (eso (F₀ F x)) renaming (fst to f*x ; snd to f*x-iso)
      ffx = f*x-iso .di.from
      ftx = f*x-iso .di.to
```

### Between categories

Above, we made an equivalence out of any fully faithful and _split_
essentially surjective functor. In set-theoretic mathematics (and indeed
between [strict categories]), the splitting condition can not be lifted
constructively: the statement "every (ff, eso) functor between strict
categories is an equivalence" is equivalent to the axiom of choice.

[univalent categories]: Cat.Univalent.html
[strict categories]: Cat.Instances.StrictCat.html

However, between [univalent categories], the situation is different: Any
essentially surjective functor splits. In particular, any functor
between univalent categories has propositional [essential fibres], so a
"mere" essential surjection is automatically split. However, note that
_both_ the domain _and_ codomain have to be categories for the argument
to go through.

[essential fibres]: Cat.Functor.Base.html#essential-fibres

```agda
module
  _ (F : Functor C D) (ccat : is-category C) (dcat : is-category D)
    (ff : is-fully-faithful F)
  where
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
```

So, suppose we have categories $\ca{C}$ and $\ca{D}$, together with a
fully faithful functor $F : \ca{C} \to \ca{D}$. For any $y : \ca{D}$,
we're given an inhabitant of $\| \sum_{x : \ca{C}} F(x) \cong y \|$,
which we want to "get out" from under the truncation. For this, we'll
show that the type being truncated is a proposition, so that we may
"untruncate" it.

```agda
  Essential-fibre-between-cats-is-prop : ∀ y → is-prop (Essential-fibre F y)
  Essential-fibre-between-cats-is-prop z (x , i) (y , j) = they're-equal where
```

For this magic trick, assume we're given a $z : \ca{D}$, together with
objects $x, y : \ca{C}$ and isomorphisms $i : F(x) \cong z$ and $j :
F(y) \cong z$. We must show that $x \equiv y$, and that over this path,
$i = j$. Since $F$ is fully faithful, we can `find an isomorphism`{.Agda
ident=is-ff→essentially-injective} $x \cong y$ in $\ca{C}$, which $F$
sends back to $i \circ j^{-1}$.

```agda
    Fx≅Fy : F₀ F x D.≅ F₀ F y
    Fx≅Fy = i D.∘Iso (j D.Iso⁻¹)

    x≅y : x C.≅ y
    x≅y = is-ff→essentially-injective {F = F} ff Fx≅Fy
```

Furthermore, since we're working with categories, these isomorphisms
restrict to _paths_ $x \equiv y$ and $F(x) \equiv F(y)$. We're
half-done: we've shown that some $p : x \equiv y$ exists, and it remains to
show that over this path we have $i \equiv j$. More specifically, we
must give a path $i \equiv j$ laying over $\id{ap}(F)(p)$.

```agda
    x≡y : x ≡ y
    x≡y = iso→path C ccat x≅y

    Fx≡Fy : F₀ F x ≡ F₀ F y
    Fx≡Fy = iso→path D dcat Fx≅Fy
```

Rather than showing it over $p : x\equiv y$ directly, we'll show it over
the path $F(x) \equiv F(y)$ we constructed independently. This is
because we can use the helper `Hom-pathp-reflr-iso`{.Agda} to establish
the result with far less computation:

```agda
    over′ : PathP (λ i → Fx≡Fy i D.≅ z) i j
    over′ = D.≅-pathp Fx≡Fy refl
      (Hom-pathp-refll-iso D dcat (D.cancell (i .D._≅_.invl)))
```

We must then connect $\id{ap}(F)(p)$ with this path $F(x) \cong
F(y)$. But since we originally got $p$ by full faithfulness of $F$, they
_are_ indeed the same path:

```agda
    abstract
      square : ap (F₀ F) x≡y ≡ Fx≡Fy
      square =
        ap (F₀ F) x≡y                       ≡⟨ F-map-path F x≅y ccat dcat ⟩
        iso→path D dcat (F-map-iso F x≅y)   ≡⟨ ap (iso→path D dcat) (equiv→section (is-ff→F-map-iso-is-equiv {F = F} ff) _)  ⟩
        iso→path D dcat Fx≅Fy               ∎

    over : PathP (λ i → F₀ F (x≡y i) D.≅ z) i j
    over = transport (λ l → PathP (λ m → square (~ l) m D.≅ z) i j) over′
```

Hence --- blink and you'll miss it --- the essential fibres of $F$ over
any $z : \ca{D}$ are propositions, so it suffices for them to be merely
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

## Isomorphisms

Another, more direct way of proving that a functor is an equivalence of
precategories is proving that it is an **isomorphism of precategories**:
It's fully faithful, thus a typal equivalence of morphisms, and in
addition its action on objects is an equivalence of types.

```agda
record is-precat-iso (F : Functor C D) : Type (adj-level C D) where
  field
    has-is-ff  : is-fully-faithful F
    has-is-iso : is-equiv (F₀ F)
```

Such a functor is (immediately) fully faithful, and the inverse
`has-is-iso`{.Agda} means that it is split essentially surjective; For
given $y : D$, the inverse of $F_0$ gives us an object $F^{-1}(y)$; We must
then provide an isomorphism $F(F^{-1}(y)) \cong y$, but those are
identical, hence isomorphic.

```agda
module _ {F : Functor C D} (p : is-precat-iso F) where
  open is-precat-iso p

  is-precat-iso→is-split-eso : is-split-eso F
  is-precat-iso→is-split-eso ob = equiv→inverse has-is-iso ob , isom
    where isom = path→iso D (equiv→section has-is-iso _)
```

Thus, by the theorem above, $F$ is an adjoint equivalence of
precategories.

```agda
  is-precat-iso→is-equivalence : is-equivalence F
  is-precat-iso→is-equivalence =
    ff+split-eso→is-equivalence has-is-ff is-precat-iso→is-split-eso
```
