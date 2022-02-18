```agda
open import Cat.Instances.StrictCat
open import Cat.Instances.Functor
open import Cat.Functor.Adjoint
open import Cat.Prelude

open import Data.Set.Coequaliser

module Cat.Thin where
```

<!--
```agda
private variable
  o h o′ h′ : Level
open Functor
open _⊣_
open _=>_
_ = refl
```
-->

# Thin categories

A category is called **thin** if all of its hom-sets are
[_propositions_] rather than sets. Furthermore, we require that the
space of objects be a set; In other words, a thin category is
necessarily [strict].

[_propositions_]: 1Lab.HLevel.html#isProp
[strict]: Cat.Instances.StrictCat.html

```agda
record isThinCat (C : Precategory o h) : Type (o ⊔ h) where
  open Precategory C
  field
    isStrict : isSet Ob
    isThin : ∀ A B → isProp (Hom A B)
```

To avoid Agda record weirdness, we package `isThinCat`{.Agda} into a
convenient packaged record together with the underlying category.

```agda
record Proset (o h : Level) : Type (lsuc (o ⊔ h)) where
  no-eta-equality
  field
    {underlying} : Precategory o h
    hasIsThin    : isThinCat underlying

  open Precategory underlying public
  open isThinCat hasIsThin public
```

The collection of all thin categories assembles into a subcategory of
`StrictCat`{.Agda}, which we call `Proset`{.Agda}.

```agda
Prosets : ∀ o h → Precategory (lsuc (o ⊔ h)) (o ⊔ h)
Prosets o h = proset where
  open Precategory
  open Proset

  proset : Precategory _ _
  proset .Ob = Proset o h
  proset .Hom C D = Functor (C .underlying) (D .underlying)
  proset .Hom-set _ D = isSet-Functor (D .isStrict)
  proset .id = Id
  proset ._∘_ = _F∘_
  proset .idr f = Functor≡ (λ _ → refl) λ _ → refl
  proset .idl f = Functor≡ (λ _ → refl) λ _ → refl
  proset .assoc f g h = Functor≡ (λ _ → refl) λ _ → refl
```

We also have a convenience function for making any set with a preorder
into a `ThinCat`{.Agda}.

```agda
module _ where
  open Proset

  makeProset : ∀ {ℓ ℓ'} {A : Type ℓ} {R : A → A → Type ℓ'}
             → isSet A
             → (∀ {x} → R x x)
             → (∀ {x y z} → R x y → R y z → R x z)
             → (∀ {x y} → isProp (R x y))
             → Proset ℓ ℓ'
  makeProset {A = A} {R} Aset Rrefl Rtrans Rprop = tc where
    open Precategory

    tc : Proset _ _
    tc .underlying .Ob          = A
    tc .underlying .Hom         = R
    tc .underlying .Hom-set _ _ = isProp→isSet Rprop
    tc .underlying .id          = Rrefl
    tc .underlying ._∘_ f g     = Rtrans g f
    tc .underlying .idr f       = Rprop _ _
    tc .underlying .idl f       = Rprop _ _
    tc .underlying .assoc f g h = Rprop _ _

    tc .hasIsThin .isThinCat.isStrict = Aset
    tc .hasIsThin .isThinCat.isThin A B x y = Rprop x y
```

# Posets

We refer to a [univalent] `thin`{.Agda ident=isThinCat} category as a
**poset**, short for partially-ordered set. Recall that a category
$\ca{C}$ is _univalent_ when the type $\sum_{(B : \ca{C})} A \cong B$ is
contractible for any fixed $A : \ca{C}$ or (more useful here) we have a
function $\mathrm{isoToPath} : A \cong B \to A \equiv B$ sending the
identity isomorphism to `refl`{.Agda}. 

In a thin category, any pair of maps $(A \to B) \times (B \ot A)$ is an
isomorphism, so in effect we have a map $(A \to B) \times (B \to A) \to
(A \equiv B)$: If a thin category is a preordered set, then a
_univalent_ thin category is a partially ordered set.

```agda
record Poset (o h : Level) : Type (lsuc (o ⊔ h)) where
  no-eta-equality
  field
    {underlying}   : Precategory o h
    hasIsThin      : isThinCat underlying
    hasIsUnivalent : isCategory underlying
    
  open Precategory underlying public
  open isThinCat hasIsThin public

  open import Cat.Univalent underlying
```

Sincce posets are most commonly considered in the context of order
theory, we abbreviate their $\hom$-props by $(a \le b)$. Similarly, we
rename the identity, composition and univalence operations to
order-theoretic names.

```agda
  _≤_ : Ob → Ob → Type h
  _≤_ = Hom
  
  reflexive : ∀ {x} → x ≤ x
  reflexive = id

  transitive : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
  transitive f g = g ∘ f
```

Any pair of opposing morphisms in a proset (thus in a poset) gives an
isomorphism. The "inversion" equations hold by thinness: Since $(f \circ
g) : A \le A$, then it must be equal to `reflexive`{.Agda} above.

```agda
  antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y
  antisym f g = isoToPath hasIsUnivalent 
    (record 
      { to = f 
      ; from = g 
      ; inverses = record 
        { invˡ = isThin _ _ _ _ ; invʳ = isThin _ _ _ _ } })
```

Forgetting the univalence datum lets us turn a `Poset`{.Agda} into a
`Proset`{.Agda}.

```agda
  →Proset : Proset o h
  →Proset .Proset.underlying = underlying
  →Proset .Proset.hasIsThin  = hasIsThin
```

## Making posets

[Rijke's theorem] says that any type equipped with a reflexive relation
$x \sim y$ which implies $x \equiv y$ is automatically a set. If $x \le
y$ is a reflexive, antisymmetric relation, we can take the relation $x
\sim y = (x \le y) \land (y \le x)$, which is evidently reflexive and,
by antisymmetry, implies $x \equiv y$.

[Rijke's theorem]: 1Lab.HLevel.Sets.html#rijkes-theorem

```agda
module _ where
  open Poset

  makePoset : ∀ {ℓ ℓ'} {A : Type ℓ} {R : A → A → Type ℓ'}
            → (∀ {x} → R x x)
            → (∀ {x y z} → R x y → R y z → R x z)
            → (∀ {x y} → R x y → R y x → x ≡ y)
            → (∀ {x y} → isProp (R x y))
            → Poset ℓ ℓ'
```

Thus, to make a poset, it suffices to have a type $A$ (any old type!), a
relation on $R$, and witnesses of reflexivity, transitivity, and
antisymmetry. We derive that $A$ is a set using Rijke's theorem as
described above, and prove that any antisymmetric proset is univalent.

```agda
  makePoset {A = A} {R} Rrefl Rtrans Rantisym Rprop = tc where
    Aset : isSet A
    Aset = Rijke-isSet {R = λ x y → R x y × R y x} 
      (Rrefl , Rrefl) 
      (λ (f , g) → Rantisym f g)
      λ x y i → Rprop (x .fst) (y .fst) i , Rprop (x .snd) (y .snd) i

    open Proset (makeProset Aset Rrefl Rtrans Rprop)
      renaming ( underlying to cat ; hasIsThin to ist )
    open import Cat.Reasoning cat

    tc : Poset _ _
    tc .underlying = cat
    tc .hasIsThin  = ist
```

For the centre of contraction, we take $A$ and the identity isomorphism.
Then, assume that we have some other object $B$ equipped with an iso $i
: A \cong B$. Since an iso is a big conjunction of propositional
components, it's a proposition, so it suffices to show $A \equiv B$. But
from the iso we have $(A \le B) \land (B \le A)$, and antisymmetry
finishes the job.

```agda
    tc .hasIsUnivalent A .centre        = A , idIso
    tc .hasIsUnivalent A .paths (B , i) = Σ≡Prop isp (Rantisym i.to i.from) where 
      module i = _≅_ i
      abstract
        isp : ∀ x → isProp (A ≅ x)
        isp ob x y i .to   = Rprop (x .to)   (y .to)   i
        isp ob x y i .from = Rprop (x .from) (y .from) i
        isp ob x y i .inverses = 
          isProp→PathP 
            (λ i → isProp-Inverses {f = Rprop (x .to)   (y .to)   i} 
                                   {g = Rprop (x .from) (y .from) i})
            (x .inverses) (y .inverses) i
```

## Monotone maps

Rather than considering _functors_ between posets, we can consider
**monotone maps** between them. This is because, since each hom-set is a
proposition, the functor identities are automatically satisfied:

```agda
module _ where
  open Poset

  Monotone : {C : Poset o h} {D : Poset o′ h′}
           → (f : C .Ob → D .Ob)
           → (∀ x y → Hom C x y → Hom D (f x) (f y))
           → Functor (C .underlying) (D .underlying)
  Monotone f ord .Functor.F₀ = f
  Monotone f ord .Functor.F₁ = ord _ _
  Monotone {D = D} f ord .Functor.F-id = D .isThin _ _ _ _
  Monotone {D = D} f ord .Functor.F-∘ _ _ = D .isThin _ _ _ _

  open Precategory

  Posets : ∀ o h → Precategory (lsuc (o ⊔ h)) (o ⊔ h)
  Posets o h .Ob = Poset o h
  Posets _ _ .Hom x y = Functor (x .underlying) (y .underlying)
  Posets _ _ .Hom-set _ d = isSet-Functor (d .isStrict)
  Posets _ _ .id = Id
  Posets _ _ ._∘_ = _F∘_
  Posets _ _ .idr f = Functor≡ (λ _ → refl) λ _ → refl
  Posets _ _ .idl f = Functor≡ (λ _ → refl) λ _ → refl
  Posets _ _ .assoc f g h = Functor≡ (λ _ → refl) λ _ → refl
```

# Prosetal reflection

There is an evident functor from $\prosets$ to $\strcat$ given by
forgetting the thinness data. This functor is ff., since maps between
prosets are functors between strict categories: it acts on morphisms
literally by the identity function.

```agda
Forget : ∀ {o h} → Functor (Prosets o h) (StrictCat o h)
Forget .F₀ C = Proset.underlying C , Proset.isStrict C
Forget .F₁ f = f
Forget .F-id = refl
Forget .F-∘ _ _ = refl
```

This functor begs the question: is it possible to freely turn a strict
category into a proset? The answer is yes! We can [propositionally
truncate] each of the $\hom$-sets. This provides a reflection of strict
categories into prosets.

[propositionally truncate]: 1Lab.HIT.Truncation.html

```agda
Free : ∀ {o h} → Functor (StrictCat o h) (Prosets o h)
Free .F₀ C = pro where
  open Precategory

  pro : Proset _ _
  pro = makeProset {R = λ x y → ∥ C .fst .Hom x y ∥} (C .snd) 
    (inc (C .fst .id)) 
    (∥-∥-elim₂ (λ _ _ → squash) λ f g → inc (C .fst ._∘_ g f)) 
    squash
```

The `Free`{.Agda} proset functor takes a strict category on the proset
obtained by truncating each of its hom-sets. This induced relation is
reflexive (by including the identity map), and transitive (by lifting
the composition map onto the truncation). On morphisms, it preserves the
object part, and lifts the morphism action onto the truncations.

```agda
Free .F₁ F .F₀      = F₀ F
Free .F₁ F .F₁      = ∥-∥-map (F₁ F)
Free .F₁ F .F-id i  = inc (F-id F i)
Free .F₁ F .F-∘ _ _ = squash _ _
Free .F-id    = Functor≡ (λ _ → refl) λ f → squash _ _
Free .F-∘ f g = Functor≡ (λ _ → refl) λ f → squash _ _
```

This `Free`{.Agda} functor is a [left adjoint] to the `Forget`{.Agda}
functor defined above, so in particular we conclude that it induces an
idempotent monad on `StrictCat`{.Agda}: The "thinning" of a
`Proset`{.Agda} is the same proset we started with.

[left adjoint]: Cat.Functor.Adjoint.html

```agda
Free⊣Forget : Free ⊣ Forget {o} {h}
Free⊣Forget .unit .η _ .F₀ x = x
Free⊣Forget .unit .η _ .F₁ = inc
Free⊣Forget .unit .η _ .F-id = refl
Free⊣Forget .unit .η _ .F-∘ f g = refl
Free⊣Forget .unit .is-natural x y f = Functor≡ (λ x → refl) λ _ → refl

Free⊣Forget .counit .η pro .F₀ x = x
Free⊣Forget .counit .η pro .F₁ = ∥-∥-elim (λ _ → pro .Proset.isThin _ _) λ x → x
Free⊣Forget .counit .η pro .F-id = refl
Free⊣Forget .counit .η pro .F-∘ f g = pro .Proset.isThin _ _ _ _
Free⊣Forget .counit .is-natural x y f = 
  Functor≡ (λ _ → refl) λ f → y .Proset.isThin _ _ _ _

Free⊣Forget .zig = Functor≡ (λ _ → refl) λ _ → squash _ _
Free⊣Forget .zag = Functor≡ (λ _ → refl) λ _ → refl
```

## Poset completions

It's also possible to freely turn a proset into a poset. We do this in a
separate module: [`Cat.Thin.Completion`](Cat.Thin.Completion.html).
