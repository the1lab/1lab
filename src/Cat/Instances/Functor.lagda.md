```agda
open import Cat.Instances.Product
open import Cat.Univalent using (isCategory)
open import Cat.Prelude

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
a set`{.Agda ident=isSet-Nat}, and equality of the components
`determines`{.Agda ident=Nat-path} equality of the transformation.

```agda
  Cat[_,_] .Hom-set F G = isSet-Nat
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
Functor≡ : {F G : Functor C D}
         → (p0 : ∀ x → F₀ F x ≡ F₀ G x)
         → (p1 : ∀ {x y} (f : C .Hom x y) 
               → PathP (λ i → D .Hom (p0 x i) (p0 y i)) (F₁ F f) (F₁ G f))
         → F ≡ G
Functor≡ p0 p1 i .F₀ x = p0 x i
Functor≡ p0 p1 i .F₁ f = p1 f i
```

<!--
```agda
Functor≡ {C = C} {D = D} {F = F} {G = G} p0 p1 i .F-id = 
  isProp→PathP (λ j → D .Hom-set _ _ (p1 (C .id) j) (D .id)) 
    (F-id F) (F-id G) i
Functor≡ {C = C} {D = D} {F = F} {G = G} p0 p1 i .F-∘ f g = 
  isProp→PathP (λ i → D .Hom-set _ _ (p1 (C ._∘_ f g) i) (D ._∘_ (p1 f i) (p1 g i)))
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
  NatIso→Iso : F [C,D].≅ G → ∀ x → F₀ F x D.≅ F₀ G x
  NatIso→Iso natiso x = 
    D.makeIso (to .η x) (from .η x) 
      (λ i → invˡ i .η x) (λ i → invʳ i .η x)
    where open [C,D]._≅_ natiso
```

We can now prove that $[C,D]$ `is a category`{.Agda ident=isCategory},
by showing that, for a fixed functor $F : C \to D$, the space of
functors $G$ equipped with natural isomorphisms $F \cong G$ is
contractible. The centre of contraction is the straightforward part: We
have the canonical choice of $(F, id)$.

<!--
```agda
module _ {C : Precategory o₁ h₁} {D : Precategory o₂ h₂} (DisCat : isCategory D) where
  import Cat.Morphism Cat[ C , D ] as [C,D]
  import Cat.Morphism D as Dm using (_≅_)
  open [C,D]
  open Cat.Univalent D hiding (isCategory)
  private module D = Precategory D
```
-->

```agda
  isCategory-Functor : isCategory Cat[ C , D ]
  isCategory-Functor F .centre = F , idIso
```

The hard part is showing that, given some other functor $G : C \to D$
with a natural isomorphism $F \cong G$, we can give a continuous
deformation $p : G \equiv F$, such that, over this $p$, the given
isomorphism looks like the identity. 

```agda
  isCategory-Functor F .paths (G , F≅G) = Σ-PathP F≡G id≡F≅G where
```

The first thing we must note is that we can recover the components of a
natural isomorphism while passing to/from paths in $D$. Since $D$ is a
category, `pathToIso`{.Agda} is an equivalence; The lemmas we need then
follow from `equivalences having sections`{.Agda ident=equiv→section}.

```agda
    ptoi-to 
      : ∀ x → pathToIso (isoToPath DisCat (NatIso→Iso F≅G _)) .Dm._≅_.to 
            ≡ F≅G .to .η x
    ptoi-to x = ap (λ e → e .Dm._≅_.to) 
      (equiv→section (isEquiv-pathToIso DisCat) _)

    ptoi-from : ∀ x → _ ≡ F≅G .from .η x
    ptoi-from x = ap (λ e → e .Dm._≅_.from) 
      (equiv→section (isEquiv-pathToIso DisCat) _)
```

We can then show that the natural isomorphism $F \cong G$ induces a
homotopy between the object parts of $F$ and $G$:

```agda
    F₀≡G₀ : ∀ x → F₀ F x ≡ F₀ G x
    F₀≡G₀ x = isoToPath DisCat (NatIso→Iso F≅G x) 
```

A slightly annoying calculation tells us that pre/post composition with
$F \cong G$ does in fact turn $F_1(f)$ into $G_1(f)$; This is because $F
\cong G$ is natural, so we can push it "past" the morphism part of $F$
so that the two halves of the isomorphism annihilate.

```agda
    F₁≡G₁ : ∀ {x y} {f : C .Hom x y} → _
    F₁≡G₁ {x = x} {y} {f} = 
      _ D.∘ F .F₁ f D.∘ _                           ≡⟨ (λ i → ptoi-to _ i D.∘ F .F₁ f D.∘ ptoi-from _ i) ⟩
      F≅G .to .η y D.∘ F .F₁ f D.∘ F≅G .from .η x   ≡⟨ ap₂ D._∘_ refl (sym (F≅G .from .is-natural _ _ _)) ∙ D.assoc _ _ _ ⟩
      (F≅G .to .η y D.∘ F≅G .from .η y) D.∘ G .F₁ f ≡⟨ ap₂ D._∘_ (λ i → F≅G .invˡ i .η y) refl ⟩
      D.id D.∘ G .F₁ f                              ≡⟨ solve D ⟩
      G .F₁ f                                       ∎

    F≡G : F ≡ G
    F≡G = Functor≡ F₀≡G₀ λ f → toHomPathP F₁≡G₁
```

Putting these homotopies together defines a path `F≡G`{.Agda}. It
remains to show that, over this path, the natural isomorphism we started
with is homotopic to the identity; Equality of `isomorphisms`{.Agda
ident=≅-PathP} and `natural transformations`{.Agda ident=Nat-pathP} are
both tested componentwise, so we can "push down" the relevant equalities
to the level of families of morphisms; By computation, all we have to
show is that $\eta{}_x \circ \mathrm{id} \circ \mathrm{id} = f$.

```agda
    id≡F≅G : PathP (λ i → F ≅ F≡G i) idIso F≅G
    id≡F≅G = ≅-PathP refl F≡G 
      (Nat-PathP refl F≡G
        λ x → toHomPathP 
          (  ap₂ D._∘_ (ptoi-to _) refl 
          ·· ap₂ D._∘_ refl (ap₂ D._∘_ refl (transport-refl _) ∙ D.idl _) 
          ·· D.idr _)) 
      (Nat-PathP F≡G refl 
        λ x → toHomPathP 
          (  ap₂ D._∘_ (transport-refl _) (D.idl _) 
          ·· D.idl _ 
          ·· ptoi-from _))
```

# Currying

There is an equivalence between the spaces of bifunctors 
$\ca{C} \times_\cat \ca{D} \to E$ and the space of functors 
$\ca{C} \to [\ca{D},E]$. We refer to the image of a functor under this
equivalence as its _exponential transpose_, and we refer to the map in
the "forwards" direction (as in the text above) as _currying_:

```agda
Curry : Functor (C ×Cat D) E → Functor C Cat[ D , E ]
Curry {C = C} {D = D} {E = E} F = curried where
  open import Cat.Functor.Bifunctor {C = C} {D = D} {E = E} F

  curried : Functor _ _
  curried .F₀ = Right
  curried .F₁ x→y = NT (λ f → first x→y) λ x y f → 
       sym (F-∘ F _ _) 
    ·· ap (F₁ F) (ap₂ _,_ (C .idr _ ∙ sym (C .idl _)) (D .idl _ ∙ sym (D .idr _))) 
    ·· F-∘ F _ _
  curried .F-id = Nat-path λ x → F-id F
  curried .F-∘ f g = Nat-path λ x → 
    ap (λ x → F₁ F (_ , x)) (sym (D .idl _)) ∙ F-∘ F _ _
```
