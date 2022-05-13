```agda
open import Algebra.Group.Cat.Base
open import Algebra.Prelude
open import Algebra.Group

open import Cat.Instances.Delooping

import Cat.Reasoning

module Algebra.Group.Ab where
```

# Abelian groups

A very important class of [groups] (which includes most familiar examples
of groups: the integers, all finite cyclic groups, etc) are those with a
_commutative_ group operation, that is, those for which $xy = yx$.
Accordingly, these have a name reflecting their importance and ubiquity:
They are called **commutative groups**. Just kidding! They're named
**abelian groups**, named after [some dude], because nothing can have
instructive names in mathematics. It's the law.

[some dude]: https://en.wikipedia.org/wiki/Niels_Henrik_Abel
[groups]: Algebra.Group.html

The theory of abelian groups is generally simpler than that of arbitrary
groups, and surprisingly the category $\ht{Ab}$ of abelian groups is
better behaved than the category $\ht{Grp}$ of possibly non-commutative
groups. This goes contrary to a common trade-off in category theory,
that of a "category of nice objects" vs a "nice category of objects" (as
an example, consider the category of fields: fields are very nice
objects algebraically, but the category of fields is utterly terrible
--- but I digress).

We define the category $\ht{Ab}$ as the [full subcategory] of the
category of groups consisting of those objects which are abelian groups.

[full subcategory]: Cat.Functor.FullSubcategory.html

```agda
Ab : ∀ ℓ → Precategory (lsuc ℓ) ℓ
Ab ℓ = Restrict {C = Groups ℓ} is-abelian-group

module Ab {ℓ} = Cat (Ab ℓ)

AbGroup : ∀ ℓ → Type (lsuc ℓ)
AbGroup _ = Ab.Ob
```

<!--
```agda
Ab-is-category : ∀ {ℓ} → is-category (Ab ℓ)
Ab-is-category = Restrict-is-category is-abelian-group
  (λ (_ , g) → let open Group-on g in hlevel 1)
  Groups-is-category

Ab→Grp : ∀ {ℓ} → Functor (Ab ℓ) (Groups ℓ)
Ab→Grp = Forget-full-subcat

module AbGrp {ℓ} (G : AbGroup ℓ) where
  ₀ : Type ℓ
  ₀ = G .object .fst

  open Group-on (G .object .snd) public

  commutative : ∀ {x y : ₀} → x ⋆ y ≡ y ⋆ x
  commutative = G .witness _ _
```
-->

This means that homomorphisms of abelian groups are the same as
homomorphisms of their underlying groups: Commutativity of the operation
is _property_, rather than structure. As a first example of the
niceness of abelian groups (or perhaps the non-niceness of general
groups), consider the following construction of a group of maps $X \to
G$:

```agda
module _ {ℓ ℓ′} (X : Type ℓ) (G : Group ℓ′) where private
  open Group-on (G .snd)

  Map-group : Group (ℓ ⊔ ℓ′)
  Map-group = _ , grp where
    grp : Group-on (X → G .fst)
    grp = make-group (hlevel 2)
      (λ _ → unit)
      (λ f g x → f x ⋆ g x)
      (λ f x → inverse (f x))
      (λ f g h i x → associative {x = f x} {y = g x} {z = h x} (~ i))
      (λ f i x → inversel {x = f x} i)
      (λ f i x → inverser {x = f x} i)
      (λ f i x → idl {x = f x} i)
```

This definition works fine for groups and maps _of sets_ into a group,
but maps of sets aren't what we're interested in when studying groups!
We'd like to equip the set $\hom_{\ht{Grp}}(A, B)$ with a group
structure induced by pointwise multiplication, but this turns out to be
possible if, and only if, the groups involved are abelian. Let us skip
the details of constructing the zero map, which is a group homomorphism
since it is constantly zero, and skip to considering sums of maps:

<!--
```agda
module _ {ℓ} (A B : AbGroup ℓ) where
  private
    module A = AbGrp A
    module B = AbGrp B
```
-->

```agda
  Hom-group : AbGroup ℓ
  Hom-group = (T , grp) , abel where
    T = Ab.Hom A B
```

<!--
```agda
    open B using (_⁻¹)
    open Group-hom renaming (pres-⋆ to p)

    zero-map : T
    zero-map .fst _ = B.unit
    zero-map .snd .p _ _ = sym B.idl
```
-->

```agda
    add-map : T → T → T
    add-map (f , fh) (g , gh) .fst x = f x B.⋆ g x
    add-map (f , fh) (g , gh) .snd .p x y =
      f (x A.⋆ y) B.⋆ g (x A.⋆ y)     ≡⟨ ap₂ B._⋆_ (fh .p x y) (gh .p x y) ⟩
      (f x B.⋆ f y) B.⋆ (g x B.⋆ g y) ≡⟨ solve-monoid B.underlying-monoid  ⟩
      f x B.⋆ (f y B.⋆ g x) B.⋆ g y   ≡⟨ (λ i → f x B.⋆ B.commutative {x = f y} {y = g x} i B.⋆ g y) ⟩
      f x B.⋆ (g x B.⋆ f y) B.⋆ g y   ≡⟨ solve-monoid B.underlying-monoid ⟩
      (f x B.⋆ g x) B.⋆ (f y B.⋆ g y) ∎
```

Note the _crucial_ third step in our calculation above: For the
pointwise sum of two group homomorphisms to be a group homomorphism, we
_must_ have that $f(y)g(x) = g(x)f(y)$. We must also use commutativity
to prove that the pointwise inverse of a group homomorphism is again a
homomorphism, as is done in the calculation below.

```agda
    inv-map : T → T
    inv-map (f , fh) .fst x = f x B.⁻¹
    inv-map (f , fh) .snd .p x y =
      f (x A.⋆ y) ⁻¹   ≡⟨ ap B.inverse (fh .p _ _) ⟩
      (f x B.⋆ f y) ⁻¹ ≡⟨ ap B.inverse B.commutative ⟩
      (f y B.⋆ f x) ⁻¹ ≡⟨ B.inv-comm ⟩
      (f x ⁻¹) B.— f y ∎

    grp : Group-on T
    grp = make-group (Ab.Hom-set A B)
      zero-map add-map inv-map
      (λ f g h → Forget-is-faithful (funext λ x → sym B.associative))
      (λ f → Forget-is-faithful (funext λ x → B.inversel))
      (λ f → Forget-is-faithful (funext λ x → B.inverser))
      (λ f → Forget-is-faithful (funext λ x → B.idl))

    abel : is-abelian-group (T , grp)
    abel f g = Forget-is-faithful (funext λ _ → B.commutative)
```

By pre/post composition, the `Hom-group`{.Agda} construction extends to
a functor $\ht{Ab}\op \times \ht{Ab} \to \ht{Ab}$, the **internal $\hom$
abelian group**.

```agda
module _ {ℓ} where
  open Functor

  Ab-hom : Functor (Ab ℓ ^op ×ᶜ Ab ℓ) (Ab ℓ)
  Ab-hom .F₀ (A , B) = Hom-group A B
  Ab-hom .F₁ {x , y} {x′ , y′} (fh , gh) = f′ where
    module g = Group-hom (gh .snd)
    f′ : Groups.Hom (Hom-group x y .object) (Hom-group x′ y′ .object)
    f′ .fst h = gh Groups.∘ h Groups.∘ fh
    f′ .snd .Group-hom.pres-⋆ (m , mh) (n , nh) = Forget-is-faithful $ funext λ i
      → g.pres-⋆ _ _

  Ab-hom .F-id = Forget-is-faithful $ funext λ i → Forget-is-faithful refl
  Ab-hom .F-∘ f g = Forget-is-faithful $ funext λ i → Forget-is-faithful refl
```

# The tensor product

We extend the category $\ht{Ab}$ defined above to a monoidal category by
equipping it with the _tensor product_ of abelian groups. Note that this
is not the only notion of "product" in $\ht{Ab}$; There is also the
"direct (bi)product" of abelian groups. The tensor product has primacy
because it defines a [left adjoint] to the internal $\hom$ functor ---
that is, homs $A \otimes B \to C$ correspond to **bilinear maps** $A, B
\to C$: functions which are "separately group homomorphisms in each
variable". By adjointness, these are the same as group homomorphisms $A
\to [B, C]$.

[left adjoint]: Cat.Functor.Adjoint.html

```agda
module _ {ℓ} (A B : AbGroup ℓ) where
  private
    module A = AbGrp A
    module B = AbGrp B
```

While the universal property of $A \otimes B$ is simple enough to state,
actually _constructing_ it is... another matter entirely. We construct
the underlying set of $A \otimes B$, written `Tensor`{.Agda} in the
code, as a massive higher inductive type:

- The first constructor is the inclusion $A \times B \to A \otimes B$
which generates the tensor product (in fact, the tensor product is a
kind of free group).

```agda
  data Tensor : Type ℓ where
    _:,_     : A.₀ → B.₀ → Tensor
```

- The next block of constructors ensures that `Tensor`{.Agda} is a
group; We add "words" to `Tensor`{.Agda}, and identify them by the group
axioms. Note that we don't need $x + 0 = x$ as a constructor.

```agda
    :0       : Tensor
    _:+_     : Tensor → Tensor → Tensor
    :inv     : Tensor → Tensor
    t-squash : is-set Tensor
    t-invl   : ∀ {x} → :inv x :+ x ≡ :0
    t-invr   : ∀ {x} → x :+ :inv x ≡ :0
    t-idl    : ∀ {x} → :0 :+ x ≡ x
    t-assoc  : ∀ {x y z} → (x :+ y) :+ z ≡ x :+ (y :+ z)
```

- The next constructor ensures that `Tensor`{.Agda} is abelian, and

```agda
    t-comm   : ∀ {x y} → x :+ y ≡ y :+ x
```

- The last two constructors encode the "universal multi-linearity": The
group operation of the tensor product, with one coordinate fixed, is
identified with the group operation of that factor.

```agda
    t-fixl   : ∀ {x y z} → (x :, y) :+ (x :, z) ≡ (x :, (y B.⋆ z))
    t-fixr   : ∀ {x y z} → (x :, z) :+ (y :, z) ≡ ((x A.⋆ y) :, z)
```

These constructors all conspire to make an abelian group $A \otimes B$.

```agda
  _⊗_ : AbGroup ℓ
  _⊗_ =
    ( Tensor
    , make-group t-squash :0 _:+_ :inv
        (λ _ _ _ → t-assoc)
        (λ _ → t-invl)
        (λ _ → t-invr)
        (λ _ → t-idl))
    , λ x y → t-comm
```

<!--
```agda
  Tensor-elim-prop
    : ∀ {ℓ′} {P : Tensor → Type ℓ′}
    → (∀ x → is-prop (P x))
    → (∀ x y → P (x :, y))
    → (∀ {x y} → P x → P y → P (x :+ y))
    → (∀ {x} → P x → P (:inv x))
    → P :0
    → ∀ x → P x
  Tensor-elim-prop {P = P} pprop ppair padd pinv pz = go where
    go : ∀ x → P x
    go (x :, y) = ppair x y
    go :0 = pz
    go (x :+ y) = padd (go x) (go y)
    go (:inv x) = pinv (go x)
    go (t-squash x y p q i j) = is-prop→squarep (λ i j → pprop (t-squash x y p q i j))
      (λ i → go x) (λ i → go (p i)) (λ i → go (q i)) (λ i → go y) i j
    go (t-invl {x} i) = is-prop→pathp (λ i → pprop (t-invl i)) (padd (pinv (go x)) (go x)) pz i
    go (t-invr {x} i) = is-prop→pathp (λ i → pprop (t-invr i)) (padd (go x) (pinv (go x))) pz i
    go (t-idl {x} i) = is-prop→pathp (λ i → pprop (t-idl i)) (padd pz (go x)) (go x) i
    go (t-assoc {x} {y} {z} i) =
      is-prop→pathp (λ i → pprop (t-assoc i))
        (padd (padd (go x) (go y)) (go z))
        (padd (go x) (padd (go y) (go z))) i
    go (t-comm {x} {y} i) =
      is-prop→pathp (λ i → pprop (t-comm i)) (padd (go x) (go y)) (padd (go y) (go x)) i
    go (t-fixl {x} {y} {z} i) = is-prop→pathp (λ i → pprop (t-fixl i)) (padd (ppair x y) (ppair x z)) (ppair x (y B.⋆ z)) i
    go (t-fixr {x} {y} {z} i) = is-prop→pathp (λ i → pprop (t-fixr i)) (padd (ppair x z) (ppair y z)) (ppair (x A.⋆ y) z) i

module _ {ℓ} {A B C : AbGroup ℓ} where
  private
    module A = AbGrp A
    module B = AbGrp B
    module C = AbGrp C
    open Group-hom
```
-->

All of those path constructors impose restrictions on mapping out of $A
\otimes B$, to the point where actually writing down its induction
principle would be wildly unpractical. Instead, we only write down the
(non-dependent) universal property: if $f : A \times B \to C$ is a
function of sets such that $f(xy, z) = f(x, z)f(y, z)$ and $f(x, yz) =
f(x, y)f(x, z)$, then it extends to an abelian group homomorphism
$\hom(A \otimes B, C)$.

```agda
  from-multilinear-map
    : (f : A.₀ → B.₀ → C.₀)
    → (∀ x y z → f (x A.⋆ y) z ≡ f x z C.⋆ f y z)
    → (∀ x y z → f z (x B.⋆ y) ≡ f z x C.⋆ f z y)
    → Ab.Hom (A ⊗ B) C
  from-multilinear-map f fixr fixl = go , record { pres-⋆ = λ _ _ → refl } where
    go : Tensor A B → C.₀
    go (x :, y) = f x y
    go (t-fixl  {x} {y} {z} i) = fixl y z x (~ i)
    go (t-fixr  {x} {y} {z} i) = fixr x y z (~ i)
```

<!--
```agda
    go :0       = C.unit
    go (x :+ y) = go x C.⋆ go y
    go (:inv x) = C.inverse (go x)
    go (t-invl  {x} i) = C.inversel {x = go x} i
    go (t-invr  {x} i) = C.inverser {x = go x} i
    go (t-idl   {x} i) = C.idl {x = go x} i
    go (t-comm  {x} {y} i) = C.commutative {x = go x} {y = go y} i
    go (t-assoc {x} {y} {z} i) = C.associative {x = go x} {y = go y} {z = go z} (~ i)
    go (t-squash x y p q i j) =
      C.has-is-set (go x) (go y) (λ i → go (p i)) (λ i → go (q i)) i j
```
-->

These multilinear maps are given by exactly the same data as a group
homomorphism $\hom(A, [B, C])$, just packaged differently. By unpacking
and re-packing that data, we can also turn those homomorphisms into ones
$\hom(A \otimes B, C)$.

```agda
  from-ab-hom : (map : Ab.Hom A (Hom-group B C)) → Ab.Hom (A ⊗ B) C
  from-ab-hom map = from-multilinear-map (λ x y → map .fst x .fst y)
    (λ x y z → happly (ap fst (map .snd .pres-⋆ x y)) z)
    (λ x y z → map .fst z .snd .pres-⋆ x y)
```

<!--
```agda
  to-ab-hom : Ab.Hom (A ⊗ B) C → Ab.Hom A (Hom-group B C)
  to-ab-hom map = go where
    go : Ab.Hom A (Hom-group B C)
    go .fst x .fst y = map .fst (x :, y)
    go .fst x .snd .pres-⋆ a b = ap (map .fst) (sym t-fixl) ∙ map .snd .pres-⋆ _ _
    go .snd .pres-⋆ a b = Forget-is-faithful $
      funext λ c → ap (map .fst) (sym t-fixr) ∙ map .snd .pres-⋆ _ _
```
-->

In fact, we can turn elements of $\hom(A \otimes B, C)$ to $\hom(A, [B,
C])$, too!  It follows, since the underlying function is preserved, that
this extends to an equivalence of $\hom$-sets $\hom(A \otimes B, C)
\cong \hom(A, [B, C])$.

```agda
  tensor⊣hom : Ab.Hom (A ⊗ B) C ≃ Ab.Hom A (Hom-group B C)
  tensor⊣hom = Iso→Equiv (to-ab-hom , iso from-ab-hom invr invl) where abstract
    invr : is-right-inverse from-ab-hom to-ab-hom
    invr f = Forget-is-faithful $ funext λ x → Forget-is-faithful refl

    invl : is-left-inverse from-ab-hom to-ab-hom
    invl f = Forget-is-faithful $ funext $
      Tensor-elim-prop _ _ (λ x → C.has-is-set _ _) (λ x y → refl)
        (λ p q → sym (f .snd .pres-⋆ _ _ ∙ ap₂ C._⋆_ (sym p) (sym q)))
        (λ p → sym (pres-inv (f .snd) ∙ ap C.inverse (sym p)))
        (sym (pres-id (f .snd)))
```

and indeed this isomorphism is one of $\hom$-groups, hence since
$\ht{Ab}$ is a univalent category, an _identification_ of $\hom$-groups.

```agda
  Tensor⊣Hom : Hom-group (A ⊗ B) C ≡ Hom-group A (Hom-group B C)
  Tensor⊣Hom = iso→path (Ab _) Ab-is-category $
    Ab.make-iso (to-ab-hom , to′) (from-ab-hom , from′)
      (Forget-is-faithful $ funext (equiv→section (tensor⊣hom .snd)))
      (Forget-is-faithful $ funext (equiv→retraction (tensor⊣hom .snd)))
```

<details>
<summary> Actually establishing that the components of
`tensor⊣hom`{.Agda} are group homomorphisms is very tedious, though!
</summary>

```agda
    where
    to′ : Group-hom (Hom-group (A ⊗ B) C .object) (Hom-group A (Hom-group B C) .object) to-ab-hom
    to′ .pres-⋆ f g = Forget-is-faithful $ funext λ x → Forget-is-faithful refl

    from′ : Group-hom (Hom-group A (Hom-group B C) .object) (Hom-group (A ⊗ B) C .object) from-ab-hom
    from′ .pres-⋆ f g = Forget-is-faithful $ funext $
      Tensor-elim-prop _ _ (λ x → C.has-is-set _ _)
        (λ x y → refl)
        (λ {x} {y} p q → ap₂ C._⋆_ p q ∙ path x y)
        (λ {x} p → ap C.inverse p
                ·· C.inv-comm
                ·· sym (ap₂ C._⋆_ (pres-inv (g′ .snd) {x = x}) (pres-inv (f′ .snd) {x = x}))
                ∙ C.commutative)
        (sym ( ap₂ C._⋆_ (pres-id (f′ .snd))
                         (pres-id (f′ .snd))
             ∙ C.idl))
      where
        f′ = from-ab-hom f
        g′ = from-ab-hom g
        path : ∀ x y → (f′ .fst x C.⋆ g′ .fst x) C.⋆ (f′ .fst y C.⋆ g′ .fst y)
                     ≡ f′ .fst (x :+ y) C.⋆ g′ .fst (x :+ y)
        path x y =
          (f′ .fst x C.⋆ g′ .fst x) C.⋆ (f′ .fst y C.⋆ g′ .fst y) ≡⟨ solve-monoid C.underlying-monoid ⟩
          f′ .fst x C.⋆ (g′ .fst x C.⋆ f′ .fst y) C.⋆ g′ .fst y   ≡⟨ (λ i → f′ .fst x C.⋆ C.commutative {x = g′ .fst x} {y = f′ .fst y} i C.⋆ g′ .fst y) ⟩
          f′ .fst x C.⋆ (f′ .fst y C.⋆ g′ .fst x) C.⋆ g′ .fst y   ≡⟨ solve-monoid C.underlying-monoid ⟩
          (f′ .fst x C.⋆ f′ .fst y) C.⋆ (g′ .fst x C.⋆ g′ .fst y) ≡˘⟨ ap₂ C._⋆_ (f′ .snd .pres-⋆ x y) (g′ .snd .pres-⋆ x y) ⟩
          f′ .fst (x :+ y) C.⋆ g′ .fst (x :+ y)                   ∎
```
</details>
