```agda
open import Cat.Instances.Product
open import Cat.Univalent using (is-category)
open import Cat.Prelude

import Cat.Reasoning

open Precategory
open Functor
open _=>_

module Cat.Instances.Functor where

private variable
  o h o₁ h₁ o₂ h₂ : Level
  C D E : Precategory o h
  F G : Functor C D
```

# Functor (pre)categories

By assigning the identity morphism to every object in $C$, we get a
natural transformation between $F : C \to D$ and itself.

```agda
idnt : {F : Functor C D} → F => F
idnt {C = C} {D = D} .η x = D .id
idnt {C = C} {D = D} .is-natural x y f = D .idl _ ∙ sym (D .idr _)
```

Given two natural transformations $\eta : F \To G$ and $\theta :
G \To H$, we can show that the assignment $x \mapsto \eta_x
\circ \theta_x$ of "componentwise compositions" defines a natural
transformation $F \To H$, which serves as the _composite_ of
$\eta$ and $\theta$.

```agda
_∘nt_ : {F G H : Functor C D} → G => H → F => G → F => H
_∘nt_ {C = C} {D = D} {F} {G} {H} f g = nat where
  module D = Precategory D

  nat : F => H
  nat .η x = f .η _ D.∘ g .η _
```

<!--
```agda
  nat .is-natural x y h =
    (f .η y D.∘ g .η y) D.∘ F.₁ h    ≡⟨ sym (D.assoc _ _ _) ⟩
    f .η y D.∘ (g .η y D.∘ F.₁ h)    ≡⟨ ap (D._∘_ (f .η y)) (g .is-natural _ _ _) ⟩
    f .η y D.∘ (G.₁ h D.∘ g .η x)    ≡⟨ D.assoc _ _ _ ⟩
    (f .η y D.∘ G.₁ h) D.∘ (g .η x)  ≡⟨ ap (λ e → e D.∘ (g .η x)) (f .is-natural _ _ _) ⟩
    (H.₁ h D.∘ f .η x) D.∘ (g .η x)  ≡⟨ sym (D.assoc _ _ _) ⟩
    H.₁ h D.∘  f .η _ D.∘ g .η  _    ∎
    where
      module C = Precategory C
      module F = Functor F
      module G = Functor G
      module H = Functor H
```
-->

We can then show that these definitions assemble into a category where
the objects are functors $F, G : C \to D$, and the morphisms are natural
transformations $F \To G$. This is because natural
transformations inherit the identity and associativity laws from the
codomain category $D$, and since hom-sets are sets, `is-natural`{.Agda}
does not matter.

```agda
module _ {o₁ h₁ o₂ h₂} (C : Precategory o₁ h₁) (D : Precategory o₂ h₂) where
  open Precategory

  Cat[_,_] : Precategory (o₁ ⊔ o₂ ⊔ h₁ ⊔ h₂) (o₁ ⊔ h₁ ⊔ h₂)
  Cat[_,_] .Ob = Functor C D
  Cat[_,_] .Hom F G = F => G
  Cat[_,_] .id = idnt
  Cat[_,_] ._∘_ = _∘nt_
```

All of the properties that make up a `Precategory`{.Agda} follow from
the characterisation of equalities in natural transformations: They `are
a set`{.Agda ident=Nat-is-set}, and equality of the components
`determines`{.Agda ident=Nat-path} equality of the transformation.

```agda
  Cat[_,_] .Hom-set F G = Nat-is-set
  Cat[_,_] .idr f = Nat-path λ x → D .idr _
  Cat[_,_] .idl f = Nat-path λ x → D .idl _
  Cat[_,_] .assoc f g h = Nat-path λ x → D .assoc _ _ _
```

Before moving on, we prove the following lemma which characterises
equality in `Functor`{.Agda} (between definitionally equal categories).
Given an identification $p : F_0(x) \equiv G_0(x)$ between the object
mappings, and an identification of morphism parts that lies over $p$, we
can identify the functors $F \equiv G$.

```agda
Functor-path : {F G : Functor C D}
         → (p0 : ∀ x → F₀ F x ≡ F₀ G x)
         → (p1 : ∀ {x y} (f : C .Hom x y)
               → PathP (λ i → D .Hom (p0 x i) (p0 y i)) (F₁ F f) (F₁ G f))
         → F ≡ G
Functor-path p0 p1 i .F₀ x = p0 x i
Functor-path p0 p1 i .F₁ f = p1 f i
```

<!--
```agda
Functor-path {C = C} {D = D} {F = F} {G = G} p0 p1 i .F-id =
  is-prop→pathp (λ j → D .Hom-set _ _ (p1 (C .id) j) (D .id))
    (F-id F) (F-id G) i
Functor-path {C = C} {D = D} {F = F} {G = G} p0 p1 i .F-∘ f g =
  is-prop→pathp (λ i → D .Hom-set _ _ (p1 (C ._∘_ f g) i) (D ._∘_ (p1 f i) (p1 g i)))
    (F-∘ F f g) (F-∘ G f g) i
```
-->

## Functor categories

When the codomain category $D$ is [univalent], then so is the category
of functors $[C,D]$. Essentially, this can be read as saying that
"naturally isomorphic functors are identified". We begin by proving that
the components of a natural isomorphism (a natural transformation with
natural inverse) are themselves isomorphisms in $D$.

[univalent]: Cat.Univalent.html

<!--
```agda
module _ {C : Precategory o h} {D : Precategory o₁ h₁} where
  import Cat.Morphism D as D
  import Cat.Morphism Cat[ C , D ] as [C,D]
```
-->

```agda
  Nat-iso→Iso : F [C,D].≅ G → ∀ x → F₀ F x D.≅ F₀ G x
  Nat-iso→Iso natiso x =
    D.make-iso (to .η x) (from .η x)
      (λ i → invl i .η x) (λ i → invr i .η x)
    where open [C,D]._≅_ natiso
```

We can now prove that $[C,D]$ `is a category`{.Agda ident=is-category},
by showing that, for a fixed functor $F : C \to D$, the space of
functors $G$ equipped with natural isomorphisms $F \cong G$ is
contractible. The centre of contraction is the straightforward part: We
have the canonical choice of $(F, id)$.

<!--
```agda
module _ {C : Precategory o₁ h₁} {D : Precategory o₂ h₂} where
  import Cat.Reasoning Cat[ C , D ] as [C,D]
  import Cat.Reasoning D as D
  open [C,D]
  open Cat.Univalent D hiding (is-category)
```
-->

```agda
  Functor-is-category : is-category D → is-category Cat[ C , D ]
  Functor-is-category _ F .centre = F , id-iso
```

The hard part is showing that, given some other functor $G : C \to D$
with a natural isomorphism $F \cong G$, we can give a continuous
deformation $p : G \equiv F$, such that, over this $p$, the given
isomorphism looks like the identity.

```agda
  Functor-is-category DisCat F .paths (G , F≅G) = Σ-pathp F≡G id≡F≅G where
```

The first thing we must note is that we can recover the components of a
natural isomorphism while passing to/from paths in $D$. Since $D$ is a
category, `path→iso`{.Agda} is an equivalence; The lemmas we need then
follow from `equivalences having sections`{.Agda ident=equiv→section}.

```agda
    ptoi-to
      : ∀ x → path→iso (iso→path DisCat (Nat-iso→Iso F≅G _)) .D._≅_.to
            ≡ F≅G .to .η x
    ptoi-to x = ap (λ e → e .D._≅_.to)
      (equiv→section (path→iso-is-equiv DisCat) _)

    ptoi-from : ∀ x → path→iso (iso→path DisCat (Nat-iso→Iso F≅G _)) .D._≅_.from
              ≡ F≅G .from .η x
    ptoi-from x = ap (λ e → e .D._≅_.from)
      (equiv→section (path→iso-is-equiv DisCat) _)
```

We can then show that the natural isomorphism $F \cong G$ induces a
homotopy between the object parts of $F$ and $G$:

```agda
    F₀≡G₀ : ∀ x → F₀ F x ≡ F₀ G x
    F₀≡G₀ x = iso→path DisCat (Nat-iso→Iso F≅G x)
```

A slightly annoying calculation tells us that pre/post composition with
$F \cong G$ does in fact turn $F_1(f)$ into $G_1(f)$; This is because $F
\cong G$ is natural, so we can push it "past" the morphism part of $F$
so that the two halves of the isomorphism annihilate.

```agda
    abstract
      F₁≡G₁ : ∀ {x y} {f : C .Hom x y}
            → PathP (λ i → D.Hom (F₀≡G₀ x i) (F₀≡G₀ y i)) (F₁ F f) (F₁ G f)
      F₁≡G₁ {x = x} {y} {f} = Hom-pathp (
        _ D.∘ F .F₁ f D.∘ _                           ≡⟨ (λ i → ptoi-to _ i D.∘ F .F₁ f D.∘ ptoi-from _ i) ⟩
        F≅G .to .η y D.∘ F .F₁ f D.∘ F≅G .from .η x   ≡⟨ ap₂ D._∘_ refl (sym (F≅G .from .is-natural _ _ _)) ∙ D.assoc _ _ _ ⟩
        (F≅G .to .η y D.∘ F≅G .from .η y) D.∘ G .F₁ f ≡⟨ ap₂ D._∘_ (λ i → F≅G .invl i .η y) refl ⟩
        D.id D.∘ G .F₁ f                              ≡⟨ solve D ⟩
        G .F₁ f                                       ∎)

    F≡G : F ≡ G
    F≡G = Functor-path F₀≡G₀ λ f → F₁≡G₁
```

Putting these homotopies together defines a path `F≡G`{.Agda}. It
remains to show that, over this path, the natural isomorphism we started
with is homotopic to the identity; Equality of `isomorphisms`{.Agda
ident=≅-pathp} and `natural transformations`{.Agda ident=Nat-pathP} are
both tested componentwise, so we can "push down" the relevant equalities
to the level of families of morphisms; By computation, all we have to
show is that $\eta{}_x \circ \id{id} \circ \id{id} = f$.

```agda
    id≡F≅G : PathP (λ i → F ≅ F≡G i) id-iso F≅G
    id≡F≅G = ≅-pathp refl F≡G
      (Nat-pathp refl F≡G
        λ x → Hom-pathp
          (  ap₂ D._∘_ (ptoi-to _) refl
          ·· ap₂ D._∘_ refl (ap₂ D._∘_ refl (transport-refl _) ∙ D.idl _)
          ·· D.idr _))
```

A useful lemma is that if you have a natural transformation where each
component is an isomorphism, the evident inverse transformation is
natural too, thus defining an inverse to `Nat-iso→Iso`{.Agda} defined
above.

```agda
module _ {C : Precategory o h} {D : Precategory o₁ h₁} {F G : Functor C D} where
  import Cat.Reasoning D as D
  import Cat.Reasoning Cat[ C , D ] as [C,D]
  private
    module F = Functor F
    module G = Functor G

  open D.is-invertible

  componentwise-invertible→invertible
    : (eta : F => G)
    → (∀ x → D.is-invertible (eta .η x))
    → [C,D].is-invertible eta
  componentwise-invertible→invertible eta invs = are-invs where
    module eta = _=>_ eta

    eps : G => F
    eps .η x = invs x .inv
    eps .is-natural x y f =
      invs y .inv D.∘ G.₁ f                             ≡⟨ ap₂ D._∘_ refl (sym (D.idr _) ∙ ap (G.₁ f D.∘_) (sym (invs x .invl))) ⟩
      invs y .inv D.∘ G.₁ f D.∘ eta.η x D.∘ invs x .inv ≡⟨ ap₂ D._∘_ refl (D.extendl (sym (eta.is-natural _ _ _))) ⟩
      invs y .inv D.∘ eta.η y D.∘ F.₁ f D.∘ invs x .inv ≡⟨ D.cancell (invs y .invr) ⟩
      F.₁ f D.∘ invs x .inv ∎

    are-invs : [C,D].is-invertible eta
    are-invs =
      record
        { inv      = eps
        ; inverses =
          record
            { invl = Nat-path λ x → invs x .invl
            ; invr = Nat-path λ x → invs x .invr
            }
        }
```

# Currying

There is an equivalence between the spaces of bifunctors
$\ca{C} \times_\cat \ca{D} \to E$ and the space of functors
$\ca{C} \to [\ca{D},E]$. We refer to the image of a functor under this
equivalence as its _exponential transpose_, and we refer to the map in
the "forwards" direction (as in the text above) as _currying_:

```agda
Curry : Functor (C ×ᶜ D) E → Functor C Cat[ D , E ]
Curry {C = C} {D = D} {E = E} F = curried where
  open import Cat.Functor.Bifunctor {C = C} {D = D} {E = E} F

  curried : Functor C Cat[ D , E ]
  curried .F₀ = Right
  curried .F₁ x→y = NT (λ f → first x→y) λ x y f →
       sym (F-∘ F _ _)
    ·· ap (F₁ F) (Σ-pathp (C .idr _ ∙ sym (C .idl _)) (D .idl _ ∙ sym (D .idr _)))
    ·· F-∘ F _ _
  curried .F-id = Nat-path λ x → F-id F
  curried .F-∘ f g = Nat-path λ x →
    ap (λ x → F₁ F (_ , x)) (sym (D .idl _)) ∙ F-∘ F _ _

Uncurry : Functor C Cat[ D , E ] → Functor (C ×ᶜ D) E
Uncurry {C = C} {D = D} {E = E} F = uncurried where
  import Cat.Reasoning C as C
  import Cat.Reasoning D as D
  import Cat.Reasoning E as E
  module F = Functor F

  uncurried : Functor (C ×ᶜ D) E
  uncurried .F₀ (c , d) = F₀ (F.₀ c) d
  uncurried .F₁ (f , g) = F.₁ f .η _ E.∘ F₁ (F.₀ _) g

  uncurried .F-id {x = x , y} = path where abstract
    path : E ._∘_ (F.₁ (C .id) .η y) (F₁ (F.₀ x) (D .id)) ≡ E .id
    path =
      F.₁ C.id .η y E.∘ F₁ (F.₀ x) D.id ≡⟨ E.elimr (F-id (F.₀ x)) ⟩
      F.₁ C.id .η y                     ≡⟨ (λ i → F.F-id i .η y) ⟩
      E.id                              ∎

  uncurried .F-∘ (f , g) (f′ , g′) = path where abstract
    path : uncurried .F₁ (f C.∘ f′ , g D.∘ g′)
         ≡ uncurried .F₁ (f , g) E.∘ uncurried .F₁ (f′ , g′)
    path =
      F.₁ (f C.∘ f′) .η _ E.∘ F₁ (F.₀ _) (g D.∘ g′)                       ≡˘⟨ E.pulll (λ i → F.F-∘ f f′ (~ i) .η _) ⟩
      F.₁ f .η _ E.∘ F.₁ f′ .η _ E.∘ F₁ (F.₀ _) (g D.∘ g′)                ≡⟨ (λ i → F.₁ f .η _ E.∘ F.₁ f′ .η _ E.∘ F-∘ (F.₀ _) g g′ i) ⟩
      F.₁ f .η _ E.∘ F.₁ f′ .η _ E.∘ F₁ (F.₀ _) g E.∘ F₁ (F.₀ _) g′       ≡⟨ solve E ⟩
      F.₁ f .η _ E.∘ (F.₁ f′ .η _ E.∘ F₁ (F.₀ _) g) E.∘ F₁ (F.₀ _) g′     ≡⟨ ap (λ e → _ E.∘ e E.∘ _) (F.₁ f′ .is-natural _ _ _) ⟩
      F.₁ f .η _ E.∘ (F₁ (F.₀ _) g E.∘ F.₁ f′ .η _) E.∘ F₁ (F.₀ _) g′     ≡⟨ solve E ⟩
      ((F.₁ f .η _ E.∘ F₁ (F.₀ _) g) E.∘ (F.₁ f′ .η _ E.∘ F₁ (F.₀ _) g′)) ∎
```

<!--
```agda
PSh : ∀ κ {o ℓ} → Precategory o ℓ → Precategory _ _
PSh κ C = Cat[ C ^op , Sets κ ]

F∘-assoc
  : ∀ {o ℓ o′ ℓ′ o′′ ℓ′′ o₃ ℓ₃}
      {C : Precategory o ℓ} {D : Precategory o′ ℓ′} {E : Precategory o′′ ℓ′′} {F : Precategory o₃ ℓ₃}
      {F : Functor E F} {G : Functor D E} {H : Functor C D}
  → F F∘ (G F∘ H) ≡ (F F∘ G) F∘ H
F∘-assoc = Functor-path (λ x → refl) λ x → refl

F∘-idl
  : ∀ {o′′ ℓ′′ o₃ ℓ₃}
      {E : Precategory o′′ ℓ′′} {F : Precategory o₃ ℓ₃}
      {F : Functor E F}
  → Id F∘ F ≡ F
F∘-idl = Functor-path (λ x → refl) λ x → refl

module
  _ {o ℓ o′ ℓ′ o′′ ℓ′′}
    {C : Precategory o ℓ} {D : Precategory o′ ℓ′} {E : Precategory o′′ ℓ′′}
  where
    private
      module DE = Cat.Reasoning Cat[ D , E ]
      module CE = Cat.Reasoning Cat[ C , E ]

    F∘-iso-l : {F F′ : Functor D E} {G : Functor C D}
             → F DE.≅ F′ → (F F∘ G) CE.≅ (F′ F∘ G)
    F∘-iso-l {F} {F′} {G} isom =
      CE.make-iso to from
        (Nat-path λ x → ap (λ e → e .η _) isom.invl)
        (Nat-path λ x → ap (λ e → e .η _) isom.invr)
      where
        module isom = DE._≅_ isom
        to : (F F∘ G) => (F′ F∘ G)
        to .η _ = isom.to .η _
        to .is-natural _ _ _ = isom.to .is-natural _ _ _

        from : (F′ F∘ G) => (F F∘ G)
        from .η _ = isom.from .η _
        from .is-natural _ _ _ = isom.from .is-natural _ _ _

module
  _ {o ℓ o′ ℓ′}
    {C : Precategory o ℓ} {D : Precategory o′ ℓ′}
  where
    private
      module DD = Cat.Reasoning Cat[ D , D ]
      module CD = Cat.Reasoning Cat[ C , D ]

    F∘-iso-id-l
      : {F : Functor D D} {G : Functor C D}
      → F DD.≅ Id → (F F∘ G) CD.≅ G
    F∘-iso-id-l {F} {G} isom = subst ((F F∘ G) CD.≅_) F∘-idl (F∘-iso-l isom)

open _=>_

whiskerl : ∀ {o ℓ o′ ℓ′ o′′ ℓ′′}
           {C : Precategory o ℓ} {D : Precategory o′ ℓ′} {E : Precategory o′′ ℓ′′}
         → {F G : Functor D E} {H : Functor C D}
         → F => G → F F∘ H => G F∘ H
whiskerl {F} {G} nt .η x = nt .η _
whiskerl {F} {G} nt .is-natural x y f = nt .is-natural _ _ _
```
-->
