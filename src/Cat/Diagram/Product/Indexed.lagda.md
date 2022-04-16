```agda
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Discrete
open import Cat.Diagram.Terminal
open import Cat.Prelude

module Cat.Diagram.Product.Indexed {o ℓ} (C : Precategory o ℓ) where
```

<!--
```agda
import Cat.Reasoning C as C
private variable
  o' ℓ' : Level
  Idx : Type ℓ'
  A B P : C.Ob
```
-->

# Indexed products

If a category admits a [terminal object] and [binary products], then it
admits products of any finite cardinality: iterate the binary product,
and use the terminal object when there aren't any objects. However,
these two classes of limit do not let us speak of products of arbitrary
cardinality, or, in the univalent context, indexed by types which are
not sets.

[terminal object]: Cat.Diagram.Terminal.html
[binary products]: Cat.Diagram.Product.html

That's where $I$-indexed products come in: Rather than having a
_functor_ giving the objects to take the limit over, we have an
arbitrary map $F$ from $I$ to the space of objects of $\ca{C}$. An
_indexed product_ for this "diagram" is then an object admitting an
universal family of maps $\pi_i : (\prod F) \to F_i$.

```
record is-indexed-product (F : Idx → C.Ob) (π : ∀ i → C.Hom P (F i))
  : Type (o ⊔ ℓ ⊔ level-of Idx) where
  no-eta-equality
  field
    ⟨_⟩     : ∀ {Y} → (∀ i → C.Hom Y (F i)) → C.Hom Y P
    commute : ∀ {i} {Y} {f : ∀ i → C.Hom Y (F i)} → π i C.∘ ⟨ f ⟩ ≡ f i
    unique  : ∀ {Y} {h : C.Hom Y P} (f : ∀ i → C.Hom Y (F i))
            → (∀ i → π i C.∘ h ≡ f i)
            → h ≡ ⟨ f ⟩

  eta : ∀ {Y} (h : C.Hom Y P) → h ≡ ⟨ (λ i → π i C.∘ h) ⟩
  eta h = unique _ λ _ → refl
```

A category $\ca{C}$ **admits indexed products** (of level $\ell$) if,
for any type $I : \ty\ \ell$ and family $F : I \to \ca{C}$, there is an
indexed product of $F$.

```agda
record Indexed-product (F : Idx → C.Ob) : Type (o ⊔ ℓ ⊔ level-of Idx) where
  no-eta-equality
  field
    {ΠF}      : C.Ob
    π         : ∀ i → C.Hom ΠF (F i)
    has-is-ip : is-indexed-product F π
  open is-indexed-product has-is-ip public

has-indexed-products : ∀ ℓ → Type _
has-indexed-products ℓ = ∀ {I : Type ℓ} (F : I → C.Ob) → Indexed-product F
```

## As limits

In the particular case where $I$ is a groupoid, e.g. because it arises
as the space of objects of a univalent category, an indexed product for
$F : I \to \ca{C}$ is the same thing as a limit over $F$, considered as
a functor $\disc{I} \to \ca{C}$. We can not lift this restriction: If
$I$ is not a groupoid, then its path spaces $x = y$ are not necessarily
sets, and so the `Disc`{.Agda} construction does not apply to it.

```agda
module _ {I : Type ℓ'} (i-is-grpd : is-groupoid I) (F : I → C.Ob) where
  open Cone-hom
  open Terminal
  open Cone

  IP→Limit : Indexed-product F → Limit {C = C} (Disc-adjunct {iss = i-is-grpd} F)
  IP→Limit IP = lim where
    module IP = Indexed-product IP

    thelim : Cone _
    thelim .apex = IP.ΠF
    thelim .ψ = IP.π
    thelim .commutes {x} =
      J (λ y p → subst (C.Hom (F x) ⊙ F) p C.id C.∘ (IP.π x) ≡ IP.π y)
        (C.eliml (transport-refl _))

    lim : Limit _
    lim .top = thelim
    lim .has⊤ x .centre .hom = IP.⟨ x .ψ ⟩
    lim .has⊤ x .centre .commutes o = IP.commute
    lim .has⊤ x .paths h = Cone-hom-path _ (sym (IP.unique _ λ i → h .commutes _))

module _ {I : Type ℓ'} (isg : is-groupoid I) (F : Functor (Disc I isg) C) where
  private module F = Functor F
  open is-indexed-product
  open Indexed-product
  open Cone-hom
  open Terminal
  open Cone

  Proj→Cone : ∀ {Y} → (∀ i → C.Hom Y (F.₀ i)) → Cone F
  Proj→Cone f .apex = _
  Proj→Cone f .ψ = f
  Proj→Cone f .commutes {x} =
    J (λ y p → F.₁ p C.∘ f x ≡ f y) (C.eliml F.F-id)

  Limit→IP : Limit {C = C} F → Indexed-product F.₀
  Limit→IP lim = the-ip where
    module lim = Cone (lim .top)

    the-ip : Indexed-product _
    the-ip .ΠF = lim.apex
    the-ip .π = lim.ψ
    the-ip .has-is-ip .⟨_⟩ f = lim .has⊤ (Proj→Cone f) .centre .hom
    the-ip .has-is-ip .commute = lim .has⊤ (Proj→Cone _) .centre .commutes _
    the-ip .has-is-ip .unique {h = h} f p i =
      lim .has⊤ (Proj→Cone f) .paths other (~ i) .hom
      where
        other : Cone-hom _ _ _
        other .hom = h
        other .commutes i = p i
```
