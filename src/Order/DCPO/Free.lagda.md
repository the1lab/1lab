<!--
```agda
open import Data.Sum

open import Cat.Displayed.Total
open import Cat.Displayed.Total
open import Cat.Functor.Adjoint
open import Cat.Prelude

open import Order.Base
open import Order.DCPO
open import Order.DCPO.Pointed
open import Order.Diagram.Lub
open import Order.Instances.Discrete
```
-->

```agda
module Order.DCPO.Free where
```

<!--
```agda
private variable
  o o' ℓ : Level
  A B C : Type ℓ

open is-directed-family
open Lub

open Functor
open _=>_
open _⊣_
```
-->

# Free DCPOs

The [discrete poset] on a set $A$ is a DCPO. To see this, note that
every semi-directed family $f : I \to A$ in a discrete poset is constant.
Furthermore, $f$ is directed, so it is merely inhabited.

```agda
Disc-is-dcpo : ∀ {ℓ} {A : Set ℓ} → is-dcpo (Disc A)
Disc-is-dcpo {A = A} .is-dcpo.directed-lubs {Ix = Ix} f dir =
  const-inhabited-fam→lub (Disc A) disc-fam-const (dir .elt)
  where
    disc-fam-const : ∀ i j → f i ≡ f j
    disc-fam-const i j =
      ∥-∥-rec! (λ (k , p , q) → p ∙ sym q)
        (dir .semidirected i j)

Disc-dcpo : (A : Set ℓ) → DCPO ℓ ℓ
Disc-dcpo A = Disc A , Disc-is-dcpo
```

This extends to a functor from $\Sets$ to the category of DCPOs.

```agda
Free-DCPO : ∀ {ℓ} → Functor (Sets ℓ) (DCPOs ℓ ℓ)
Free-DCPO .F₀ = Disc-dcpo
Free-DCPO .F₁ f =
  to-scott-directed f λ s dir x x-lub →
  const-inhabited-fam→is-lub (Disc _)
    (λ ix → ap f (disc-is-lub→const x-lub ix))
    (dir .elt)
Free-DCPO .F-id = scott-path (λ _ → refl)
Free-DCPO .F-∘ _ _ = scott-path (λ _ → refl)
```

Furthermore, this functor is left adjoint to the forgetful functor
to $\Sets$.

```agda
Free-DCPO⊣Forget-DCPO : ∀ {ℓ} → Free-DCPO {ℓ} ⊣ Forget-DCPO
Free-DCPO⊣Forget-DCPO .unit .η _ x = x
Free-DCPO⊣Forget-DCPO .unit .is-natural _ _ _ = refl
Free-DCPO⊣Forget-DCPO .counit .η D =
  to-scott-directed (λ x → x) λ s dir x x-lub → λ where
    .is-lub.fam≤lub i → path→≤ (disc-is-lub→const x-lub i)
    .is-lub.least y le →
      ∥-∥-rec ≤-thin
        (λ i →
          x   =˘⟨ disc-is-lub→const x-lub i ⟩
          s i ≤⟨ le i ⟩
          y   ≤∎)
        (dir .elt)
   where open DCPO D
Free-DCPO⊣Forget-DCPO .counit .is-natural x y f =
  scott-path (λ _ → refl)
Free-DCPO⊣Forget-DCPO .zig = scott-path (λ _ → refl)
Free-DCPO⊣Forget-DCPO .zag = refl
```

# Free Pointed DCPOs

We construct the free [pointed DCPO] on a set $A$; IE a pointed
DCPO $A_{\bot}$ with the property that for all pointed DCPOs $B$,
functions $A \to B$ correspond with strictly Scott-continuous maps
$A_{\bot} \to B$.

[pointed DCPO]: Order.DCPO.Pointed.html

To start, we define a type of **partial elements** of $A$ as a pair
of a proposition $\varphi$, along with a function $\varphi \to A$.

```agda
record Part {ℓ} (A : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    def : Ω
    elt : ∣ def ∣ → A

open Part
```

We say that a partial element $x$ is **defined** when the associated
proposition is true, and write $x \downarrow y$ to denote that $x$
is defined, and it's value is $y$.

```agda
is-defined : Part A → Type
is-defined x? = ∣ x? .def ∣

_↓_ : Part A → A → Type _
x ↓ y = Σ[ d ∈ is-defined x ] (x .elt d ≡ y)
```

We can embed $A$ into the type of partial elements by using $\top$
as our choice of proposition.

```agda
always : A → Part A
always a .def = el ⊤ (hlevel 1)
always a .elt _ = a

always-inj : ∀ {x y : Type ℓ} → always x ≡ always y → x ≡ y
always-inj {x = x} p =
  J (λ y p → (d : is-defined y) → x ≡ y .elt d) (λ _ → refl) p tt
```

Next, we note that the type of partial elements forms a [monad].

[monad]: Cat.Diagram.Monad.html

```agda
part-map : (A → B) → Part A → Part B
part-map f x .def = x .def
part-map f x .elt px = f (x .elt px)

part-ap : Part (A → B) → Part A → Part B
part-ap f x .def = el (is-defined f × is-defined x) hlevel!
part-ap f x .elt (pf , px) = f .elt pf (x .elt px)

part-bind : Part A → (A → Part B) → Part B
part-bind x f .def =
  el (Σ[ px ∈ is-defined x ] is-defined (f (x .elt px))) hlevel!
part-bind x f .elt (px , pfx) =
  f (x .elt px) .elt pfx
```

<!--
```agda
instance
  Part-Map : Map (eff Part)
  Part-Map .Map._<$>_ = part-map

  Part-Idiom : Idiom (eff Part)
  Part-Idiom .Idiom.Map-idiom = Part-Map
  Part-Idiom .Idiom.pure = always
  Part-Idiom .Idiom._<*>_ = part-ap

  Part-Bind : Bind (eff Part)
  Part-Bind .Bind._>>=_ = part-bind
  Part-Bind .Bind.Idiom-bind = Part-Idiom
```
-->

Paths between partial elements are given by bi-implications of their
propositions, along with a path between their values, assuming that both
elements are defined.

```agda
Part-pathp
  : {x : Part A} {y : Part B}
  → (p : A ≡ B)
  → (q : x .def ≡ y .def)
  → PathP (λ i → ∣ q i ∣ → p i) (x .elt) (y .elt)
  → PathP (λ i → Part (p i)) x y
Part-pathp {x = x} {y = y} p q r i .def = q i
Part-pathp {x = x} {y = y} p q r i .elt = r i

part-ext
  : ∀ {x y : Part A}
  → (to : is-defined x → is-defined y)
  → (from : is-defined y → is-defined x)
  → (∀ (x-def : is-defined x) (y-def : is-defined y) → x .elt x-def ≡ y .elt y-def)
  → x ≡ y
part-ext to from p =
  Part-pathp refl
    (Ω-ua to from)
    (funext-dep (λ _ → p _ _))
```

<!--
```agda
Part-is-hlevel : ∀ {A : Type ℓ} → ∀ n → is-hlevel A (2 + n) → is-hlevel (Part A) (2 + n)
Part-is-hlevel n hl = Iso→is-hlevel (2 + n) eqv $
  Σ-is-hlevel (2 + n) hlevel! λ _  →
  Π-is-hlevel (2 + n) λ _ → hl
  where unquoteDecl eqv = declare-record-iso eqv (quote Part)

Part-is-set : is-set A → is-set (Part A)
Part-is-set = Part-is-hlevel 0

part-map-id : ∀ (x : Part A) → part-map (λ a → a) x ≡ x
part-map-id x =
  part-ext (λ p → p) (λ p → p)
    (λ _ _ → ap (x .elt) (x .def .is-tr _ _))

part-map-∘
  : ∀ (f : B → C) (g : A → B)
  → ∀ (x : Part A) → part-map (f ⊙ g) x ≡ part-map f (part-map g x)
part-map-∘ f g x =
  part-ext (λ p → p) (λ p → p)
    (λ _ _ → ap (f ⊙ g ⊙ x .elt) (x .def .is-tr _ _))
```
-->

We say that a partial element $y$ **refines** $x$ if $y$ is defined
whenever $x$ is, and their values are equal whenever $x$ is defined.

```
record _⊑_ {ℓ} {A : Type ℓ} (x y : Part A) : Type ℓ where
  no-eta-equality
  field
    implies : is-defined x → is-defined y
    refines : (x-def : is-defined x) → (y .elt (implies x-def) ≡ x .elt x-def)

open _⊑_
```

<!--
```agda
⊑-is-hlevel : ∀ {x y : Part A} → ∀ n → is-hlevel A (2 + n) → is-hlevel (x ⊑ y) (suc n)
⊑-is-hlevel {x = x} {y = y} n hl = Iso→is-hlevel (suc n) eqv $
  Σ-is-hlevel (suc n) (Π-is-hlevel (suc n) λ _ → is-prop→is-hlevel-suc (y .def .is-tr)) λ _ →
  Π-is-hlevel (suc n) λ _ → hl _ _
  where unquoteDecl eqv = declare-record-iso eqv (quote _⊑_) 
```
-->

This ordering is reflexive, transitive, and anti-symmetric, so the type
of partial elements forms a poset whenever $A$ is a set.

```
⊑-refl : ∀ {x : Part A} → x ⊑ x
⊑-refl .implies x-def = x-def
⊑-refl .refines _ = refl

⊑-thin : ∀ {x y : Part A} → is-set A → is-prop (x ⊑ y)
⊑-thin A-set = ⊑-is-hlevel 0 A-set

⊑-trans : ∀ {x y z : Part A} → x ⊑ y → y ⊑ z → x ⊑ z
⊑-trans p q .implies x-def = q .implies (p .implies x-def)
⊑-trans p q .refines x-def = q .refines (p .implies x-def) ∙ p .refines x-def

⊑-antisym : ∀ {x y : Part A} → x ⊑ y → y ⊑ x → x ≡ y
⊑-antisym {x = x} {y = y} p q = part-ext (p .implies) (q .implies) λ x-def y-def →
  ap (x .elt) (x .def .is-tr _ _) ∙ q .refines y-def

Parts : (A : Set ℓ) → Poset ℓ ℓ
Parts A = to-poset (Part ∣ A ∣) mk-parts where
  mk-parts : make-poset _ (Part ∣ A ∣)
  mk-parts .make-poset.rel = _⊑_
  mk-parts .make-poset.id = ⊑-refl
  mk-parts .make-poset.thin = ⊑-thin (A .is-tr)
  mk-parts .make-poset.trans = ⊑-trans
  mk-parts .make-poset.antisym = ⊑-antisym
```

The monad structure defined earlier respects the refinement ordering.

```agda
part-map-⊑
  : ∀ {f : A → B} {x y : Part A}
  → x ⊑ y → part-map f x ⊑ part-map f y
part-map-⊑ p .implies = p .implies
part-map-⊑ {f = f} p .refines d = ap f (p .refines d)
```

Furthermore, the poset of partial elements has [least upper bounds] of all
[semidirected families].

[least upper bounds]: Order.Diagram.Lub.html
[semidirected families]: Order.DCPO.html

```agda
⊑-lub
  : ∀ {Ix : Type ℓ}
  → is-set A
  → (s : Ix → Part A)
  → (∀ i j → ∃[ k ∈ Ix ] (s i ⊑ s k × s j ⊑ s k))
  → Part A
```

Let $s : I \to A$ be a semidirected family, IE: for every $i, j : I$, there
merely exists some $k : I$ such that $s(i) \lsq s(k)$ and $s(j) \lsq s(k)$.
The least upper bound of $s$ shall be defined whenever there merely exists
some $i : I$ such that $s(i)$ is defined.

```agda
⊑-lub {Ix = Ix} set s dir .def = elΩ (Σ[ i ∈ Ix ] is-defined (s i))
```

Next, we need to construct an element of $A$ under the assumption that
there exists such an $i$. The obvious move is to use the value of $s(i)$,
though this is hindered by the fact that there only _merely_ exists an
$i$. However, as $A$ is a set, it suffices to show that the map
$(i , \varphi_i) \mapsto s(i)(\varphi_i)$ is constant.

```
⊑-lub {Ix = Ix} set s dir .elt =
  □-rec-set 
    (λ pi → s (fst pi) .elt (snd pi))
    (λ p q i →
      is-const p q i .elt $
      is-prop→pathp (λ i → (is-const p q i) .def .is-tr) (p .snd) (q .snd) i)
    set
  where abstract
```

To see this, we use the fact that $s$ is semidirected to obtain a $k$
such that $s(i), s(j) \lsq s(k)$. We can then use the fact that $s(k)$
refines both $s(i)$ and $s(j)$ to obtain the desired path.

```agda
    is-const
      : ∀ (p q : Σ[ i ∈ Ix ] is-defined (s i))
      → s (p .fst) ≡ s (q .fst)
    is-const (i , si) (j , sj) = ∥-∥-proj {ap = Part-is-set set _ _} $ do
      (k , p , q) ← dir i j
      pure $ part-ext (λ _ → sj) (λ _ → si) λ si sj →
        s i .elt si              ≡˘⟨ p .refines si ⟩
        s k .elt (p .implies si) ≡⟨ ap (s k .elt) (s k .def .is-tr _ _) ⟩
        s k .elt (q .implies sj) ≡⟨ q .refines sj ⟩
        s j .elt sj              ∎
```

Next, we show that this actually defines a least upper bound. This is
pretty straightforward, so we do not dwell on it too deeply.

```agda
⊑-lub-le
  : ∀ {Ix : Type ℓ}
  → {set : is-set A}
  → {s : Ix → Part A}
  → {dir : ∀ i j → ∃[ k ∈ Ix ] (s i ⊑ s k × s j ⊑ s k)}
  → ∀ i → s i ⊑ ⊑-lub set s dir
⊑-lub-le i .implies si = inc (i , si)
⊑-lub-le i .refines si = refl

⊑-lub-least
  : ∀ {Ix : Type ℓ}
  → {set : is-set A}
  → {s : Ix → Part A}
  → {dir : ∀ i j → ∃[ k ∈ Ix ] (s i ⊑ s k × s j ⊑ s k)}
  → ∀ x → (∀ i → s i ⊑ x) → ⊑-lub set s dir ⊑ x
⊑-lub-least {Ix = Ix} {set = set} {s = s} {dir = dir} x le .implies =
  □-rec! λ si → le (si .fst) .implies (si .snd)
⊑-lub-least {Ix = Ix} {set = set} {s = s} {dir = dir} x le .refines =
 □-elim (λ _ → set _ _) λ (i , si) → le i .refines si
```

<!--
```agda
part-map-lub
  : ∀ {Ix : Type ℓ}
  → {A : Set o} {B : Set o'}
  → {s : Ix → Part ∣ A ∣}
  → {dir : ∀ i j → ∃[ k ∈ Ix ] (s i ⊑ s k × s j ⊑ s k)}
  → (f : ∣ A ∣ → ∣ B ∣)
  → is-lub (Parts B) (part-map f ⊙ s) (part-map f (⊑-lub (A .is-tr) s dir))
part-map-lub f .is-lub.fam≤lub i = part-map-⊑ (⊑-lub-le i)
part-map-lub f .is-lub.least y le .implies =
  □-rec! λ si → le (si .fst) .implies (si .snd)
part-map-lub {B = B} f .is-lub.least y le .refines =
  □-elim (λ _ → B .is-tr _ _) λ si → le (si .fst) .refines (si .snd)
```
-->

Therefore, the type of partial elements forms a DCPO.

```agda
Parts-is-dcpo : ∀ {A : Set ℓ} → is-dcpo (Parts A)
Parts-is-dcpo {A = A} .is-dcpo.directed-lubs s dir .Lub.lub =
  ⊑-lub (A .is-tr) s (dir .semidirected)
Parts-is-dcpo {A = A} .is-dcpo.directed-lubs s dir .Lub.has-lub .is-lub.fam≤lub =
  ⊑-lub-le
Parts-is-dcpo {A = A} .is-dcpo.directed-lubs s dir .Lub.has-lub .is-lub.least =
  ⊑-lub-least

Parts-dcpo : (A : Set ℓ) → DCPO ℓ ℓ
Parts-dcpo A = Parts A , Parts-is-dcpo
```

Furthermore, it forms a pointed DCPO, as it has least upper bounds of
all semidirected families. However, we opt to explicitly construct a
bottom for computational reasons.

```agda
never : Part A
never .def = el ⊥ (hlevel 1)

never-⊑ : ∀ {x : Part A} → never ⊑ x
never-⊑ .implies ()
never-⊑ .refines ()


part-map-never : ∀ {f : A → B} {x} → part-map f never ⊑ x
part-map-never .implies ()
part-map-never .refines ()

Parts-is-pointed-dcpo : ∀ {A : Set ℓ} → is-pointed-dcpo (Parts-dcpo A)
Parts-is-pointed-dcpo .Bottom.bot = never
Parts-is-pointed-dcpo .Bottom.has-bottom _ = never-⊑

Parts-pointed-dcpo : ∀ (A : Set ℓ) → Pointed-dcpo ℓ ℓ
Parts-pointed-dcpo A = Parts-dcpo A , Parts-is-pointed-dcpo
```

```agda
Free-Pointed-dcpo : Functor (Sets ℓ) (Pointed-DCPOs ℓ ℓ)
Free-Pointed-dcpo .F₀ A =
  Parts-pointed-dcpo A
Free-Pointed-dcpo .F₁ {x = A} f =
  to-strict-scott-bottom (part-map f)
    (λ _ _ → part-map-⊑)
    (λ _ _ → part-map-lub {A = A} f)
    (λ _ → part-map-never)
Free-Pointed-dcpo .F-id =
  strict-scott-path part-map-id
Free-Pointed-dcpo .F-∘ f g =
  strict-scott-path (part-map-∘ f g)
```

<!--
```agda
always-⊑
  : ∀ {x : Part A} {y : A}
  → (∀ (d : is-defined x) → x .elt d ≡ y) → x ⊑ always y
always-⊑ p .implies _ = tt
always-⊑ p .refines d = sym (p d)

always-⊒ 
  : ∀ {x : A} {y : Part A}
  → (p : is-defined y) → x ≡ y .elt p
  → always x ⊑ y
always-⊒ p q .implies _ = p
always-⊒ p q .refines _ = sym q

always-natural
  : ∀ {x : A} → (f : A → B) → part-map f (always x) ≡ always (f x)
always-natural f = part-ext (λ _ → tt) (λ _ → tt) λ _ _ → refl
```
-->

```
module _ (D : Pointed-dcpo o ℓ) where
  open Pointed-dcpo D

  part-counit : Part Ob → Ob
  part-counit x = ⋃-prop (x .elt ⊙ Lift.lower) def-prop
    where abstract
      def-prop : is-prop (Lift o (is-defined x))
      def-prop = hlevel!

  part-counit-elt : (x : Part Ob) → (p : is-defined x) → part-counit x ≡ x .elt p
  part-counit-elt x p =
    ≤-antisym
      (⋃-prop-least _ _ _ λ (lift p') → path→≤ (ap (x .elt) (x .def .is-tr _ _)))
      (⋃-prop-le _ _ (lift p))

  part-counit-⊑ : (x y : Part Ob) → x ⊑ y → part-counit x ≤ part-counit y
  part-counit-⊑ x y p =
    ⋃-prop-least _ _ (part-counit y) λ (lift i) →
      x .elt i                       =˘⟨ p .refines i ⟩
      y .elt (p .implies i)          ≤⟨ ⋃-prop-le _ _ (lift (p .implies i)) ⟩
      ⋃-prop (y .elt ⊙ Lift.lower) _ ≤∎

  part-counit-lub
    : {Ix : Type o}
    → (s : Ix → Part Ob)
    → (sdir : is-semidirected-family (Parts set) s)
    → is-lub poset (part-counit ⊙ s) (part-counit (⊑-lub (set .is-tr) s sdir))
  part-counit-lub s sdir .is-lub.fam≤lub i =
    ⋃-prop-least _ _ _ λ (lift p) →
    ⋃-prop-le _ _ (lift (inc (i , p)))
  part-counit-lub {Ix = Ix} s sdir .is-lub.least y le =
    ⋃-prop-least _ _ _ $ λ (lift p) →
    □-elim (λ p → ≤-thin {x = ⊑-lub _ s sdir .elt p}) (λ where
      (i , si) →
        s i .elt si ≤⟨ ⋃-prop-le _ _ (lift si) ⟩
        ⋃-prop _ _  ≤⟨ le i ⟩
        y           ≤∎)
      p

  part-counit-never
    : ∀ x → part-counit never ≤ x
  part-counit-never x = ⋃-prop-least _ _ x (absurd ⊙ Lift.lower)
```


```agda
Free-Pointed-dcpo⊣Forget-Pointed-dcpo
  : ∀ {ℓ} → Free-Pointed-dcpo {ℓ} ⊣ Forget-Pointed-dcpo
Free-Pointed-dcpo⊣Forget-Pointed-dcpo .unit .η A x = always x
Free-Pointed-dcpo⊣Forget-Pointed-dcpo .unit .is-natural x y f =
  funext λ _ → sym (always-natural f)
Free-Pointed-dcpo⊣Forget-Pointed-dcpo .counit .η D =
  to-strict-scott-bottom (part-counit D)
    (part-counit-⊑ D)
    (λ s dir → part-counit-lub D s (dir .semidirected))
    (part-counit-never D)
Free-Pointed-dcpo⊣Forget-Pointed-dcpo .counit .is-natural D E f =
  strict-scott-path λ x → sym $ Strict-scott.pres-⋃-prop f _ _ _
Free-Pointed-dcpo⊣Forget-Pointed-dcpo .zig {A} =
  strict-scott-path λ x →
    part-ext
      (A?.⋃-prop-least _ _ x (λ p → always-⊒ (Lift.lower p) refl) .implies)
      (λ p → A?.⋃-prop-le _ _ (lift p) .implies tt)
      (λ p q →
        sym (A?.⋃-prop-least _ _ x (λ p → always-⊒ (Lift.lower p) refl) .refines p)
        ∙ ap (x .elt) (x .def .is-tr _ _))
  where module A? = Pointed-dcpo (Parts-pointed-dcpo A)
Free-Pointed-dcpo⊣Forget-Pointed-dcpo .zag {B} =
   funext λ x →
     sym $ lub-of-const-fam B.poset (λ _ _ → refl) (B.⋃-prop-lub _ _ ) (lift tt)
    where module B = Pointed-dcpo B
```
