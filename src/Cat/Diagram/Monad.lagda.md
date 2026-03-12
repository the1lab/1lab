<!--
```agda
open import Cat.Functor.FullSubcategory
open import Cat.Displayed.Univalence
open import Cat.Functor.Conservative
open import Cat.Functor.Properties
open import Cat.Displayed.Total
open import Cat.Functor.Adjoint
open import Cat.Displayed.Base
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Displayed.Morphism
import Cat.Functor.Reasoning
import Cat.Reasoning

open _=>_ using (is-natural)
open Displayed
open Functor
open ∫Hom
```
-->

```agda
module Cat.Diagram.Monad where
```

<!--
```agda
module _ {o h : _} {C : Precategory o h} where
  private module C = Cat.Reasoning C
```
-->

# Monads {defines=monad}

A **monad on a category** $\cC$ is one way of categorifying the concept
of [monoid]. Specifically, rather than living in a monoidal category, a
monad lives in a bicategory. Here, we concern ourselves with the case of
monads in the bicategory of categories,[^general] so that we may say: 
A monad is an endofunctor $M$, equipped with a `unit`{.Agda} natural 
transformation $\Id \To M$, and a `multiplication`{.Agda ident=mult} 
$(M \circ M) \To M$.

[^general]: 
  See [[monad in a bicategory|monad in]] for the more general case.

More generally, we define what it means to equip a *fixed* functor $M$
with the structure of a monad. The notion of "monad on a category" is
obtained by pairing the functor $M$ with the monad structure $\eta,
\mu$.

[monoid]: Algebra.Monoid.html

```agda
  record Monad-on (M : Functor C C) : Type (o ⊔ h) where
    no-eta-equality
    field
      unit : Id => M
      mult : M F∘ M => M
```

<!--
```agda
    module unit = _=>_ unit
    module mult = _=>_ mult

    open Functor M renaming (F₀ to M₀ ; F₁ to M₁ ; F-id to M-id ; F-∘ to M-∘) public
    open mult renaming (η to μ) using () public
    open unit using (η) public
```
-->

Furthermore, these natural transformations must satisfy identity and
associativity laws exactly analogous to those of a monoid.

```agda
    field
      μ-unitr : ∀ {x} → μ x C.∘ M₁ (η x) ≡ C.id
      μ-unitl : ∀ {x} → μ x C.∘ η (M₀ x) ≡ C.id
      μ-assoc : ∀ {x} → μ x C.∘ M₁ (μ x) ≡ μ x C.∘ μ (M₀ x)
```

# Algebras over a monad {defines="monad-algebra algebra-over-a-monad algebras-over-a-monad"}

One way of interpreting a monad $M$ is as giving a _signature_ for an
algebraic theory. For instance, the [[free monoid]] monad describes the
signature for the theory of monoids, and the [[free group|free group
construction]] monad describes the theory of groups.

Under this light, an **algebra over a monad** is a way of _evaluating_
the abstract operations given by a monadic expression to a concrete
value. Formally, an algebra for $M$ is given by a choice of object $A$
and a morphism $\nu : M(A) \to A$.

```agda
  record Algebra-on {F} (M : Monad-on F) (ob : ⌞ C ⌟) : Type (o ⊔ h) where
    no-eta-equality
    open Monad-on M

    field
      ν : C.Hom (M₀ ob) ob
```

This morphism must satisfy equations categorifying those which define a
monoid action. If we think of $M$ as specifying a signature of
_effects_, then `v-unit`{.Agda} says that the `unit`{.Agda} has no
effects, and `v-mult`{.Agda} says that, given two layers $M(M(A))$, it
doesn't matter whether you first join then evaluate, or evaluate twice.

```agda
      ν-unit : ν C.∘ η ob ≡ C.id
      ν-mult : ν C.∘ μ ob ≡ ν C.∘ M₁ ν
```

<!--
```agda
  private
    unquoteDecl eqv = declare-record-iso eqv (quote Algebra-on)

  Algebra-on-pathp
    : ∀ {F} {M : Monad-on F} {X Y} (p : X ≡ Y) {A : Algebra-on M X} {B : Algebra-on M Y}
    → PathP (λ i → C.Hom (F · p i) (p i)) (A .Algebra-on.ν) (B .Algebra-on.ν)
    → PathP (λ i → Algebra-on M (p i)) A B
  Algebra-on-pathp over mults = injectiveP (λ _ → eqv) (mults ,ₚ prop!)

instance
  Extensional-Algebra-on
    : ∀ {o ℓ ℓr} {C : Precategory o ℓ} {F : Functor C C} {M : Monad-on F}
    → (let open Precategory C)
    → ∀ {X}
    → ⦃ sa : Extensional (Hom (F · X) X) ℓr ⦄
    → Extensional (Algebra-on M X) ℓr
  Extensional-Algebra-on {C = C} ⦃ sa ⦄ =
    injection→extensional! (Algebra-on-pathp refl) sa

Monad : ∀ {o ℓ} (C : Precategory o ℓ) → Type _
Monad C = Σ[ F ∈ Functor C C ] (Monad-on F)
```
-->

# Eilenberg-Moore category {defines=eilenberg-moore-category}

If we take a monad $M$ as the signature of an (algebraic) theory, and
$M$-algebras as giving _models_ of that theory, then we can ask (like
with everything in category theory): Are there maps between
interpretations? The answer (as always!) is yes: An `algebra
homomorphism`{.Agda ident=Algebra-hom} is a map of the underlying
objects which "commutes with the algebras".

We can be more specific about "commuting with the algebras" by drawing a
square: A map $m : X \to Y$ in the ambient category is a homomorphism of
$M$-algebras when the square below commutes.

~~~{.quiver}
\[\begin{tikzcd}
  {M(X)} && {M(Y)} \\
  \\
  {X} && {Y}
  \arrow["{M_1(m)}", from=1-1, to=1-3]
  \arrow["{\nu}"', from=1-1, to=3-1]
  \arrow["{\nu\prime}", from=1-3, to=3-3]
  \arrow["m"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

We can assemble $M$-algebras and their homomorphisms into a
[[displayed category]] over $\cC$: the type of objects over some $A$
consists of all possible algebra structures on $A$, and the type of
morphisms over $f : \cC(A,B)$ are proofs that $f$ is an $M$-algebra
homomorphism.

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} {F : Functor C C} (M : Monad-on F) where
  private
    module C = Cat.Reasoning C
    module M = Monad-on M
    module MR = Cat.Functor.Reasoning F
  open Algebra-on
  open M
```
-->

```agda
  Monad-algebras : Displayed C (o ⊔ ℓ) ℓ
  Monad-algebras = with-thin-display record where
    Ob[_]        = Algebra-on M
    Hom[_] f α β = f C.∘ α .ν ≡ β .ν C.∘ M₁ f
```

Defining the identity and composition maps is mostly an exercise in
categorical yoga:

```agda
    id' {X} {α} =
      C.id C.∘ α .ν    ≡⟨ C.idl _ ∙ C.intror M-id ⟩
      α .ν C.∘ M₁ C.id ∎
    _∘'_ {_} {_} {_} {α} {β} {γ} {f = f} {g = g} p q =
      (f C.∘ g) C.∘ α .ν       ≡⟨ C.pullr q ⟩
      f C.∘ β .ν C.∘ M₁ g      ≡⟨ C.pulll p ⟩
      (γ .ν C.∘ M₁ f) C.∘ M₁ g ≡⟨ C.pullr (sym (M-∘ _ _)) ⟩
      γ .ν C.∘ M₁ (f C.∘ g)    ∎
```

The [[total category]] of this displayed category is referred
to as the **Eilenberg-Moore** category of $M$.

```agda
  Eilenberg-Moore : Precategory (o ⊔ ℓ) ℓ
  Eilenberg-Moore = ∫ Monad-algebras

  private
    module EM = Cat.Reasoning Eilenberg-Moore

  Algebra : Type _
  Algebra = EM.Ob

  Algebra-hom : (X Y : Algebra) → Type _
  Algebra-hom X Y = EM.Hom X Y
```

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} {F : Functor C C} {M : Monad-on F} where
  private
    module C = Cat.Reasoning C
    module M = Monad-on M
    module MR = Cat.Functor.Reasoning F
    module EM = Cat.Reasoning (Eilenberg-Moore M)
  open M
  open Algebra-on

  instance
    Extensional-Algebra-Hom
      : ∀ {ℓr} {a b} {A : Algebra-on M a} {B : Algebra-on M b}
      → ⦃ sa : Extensional (C.Hom a b) ℓr ⦄
      → Extensional (Algebra-hom M (a , A) (b , B)) ℓr
    Extensional-Algebra-Hom ⦃ sa ⦄ = injection→extensional!
      (λ p → ∫Hom-path (Monad-algebras M) p prop!) sa
```
-->

By projecting the underlying object of the algebras, and the underlying
morphisms of the homomorphisms between them, we can define a functor
from `Eilenberg-Moore`{.Agda} back to the underlying category.
In prose, we denote this functor as $U : \cC^M \to \cC$.

```agda
  Forget-EM : Functor (Eilenberg-Moore M) C
  Forget-EM = πᶠ (Monad-algebras M)
```

This functor is [[faithful]] as the maps in the Eilenberg-Moore category
are structured maps of $\cC$.

```agda
  Forget-EM-is-faithful : is-faithful Forget-EM
  Forget-EM-is-faithful = ext
```

Moreover, this functor is [[conservative]]. This follows from a bit of
routine algebra.

```agda
  Forget-EM-is-conservative : is-conservative Forget-EM
  Forget-EM-is-conservative {X , α} {Y , β} {f = f} f-inv =
    EM.make-invertible f-alg-inv (ext invl) (ext invr)
    where
      open C.is-invertible f-inv

      f-alg-inv : Algebra-hom M (Y , β) (X , α)
      f-alg-inv .fst = inv
      f-alg-inv .snd =
        inv C.∘ β .ν                                 ≡⟨ ap₂ C._∘_ refl (C.intror (MR.annihilate invl)) ⟩
        inv C.∘ β .ν C.∘ M₁ (f .fst) C.∘ M.M₁ inv    ≡⟨ ap₂ C._∘_ refl (C.extendl (sym (f .snd))) ⟩
        inv C.∘ f .fst C.∘ α .ν C.∘ M.M₁ inv         ≡⟨ C.cancell invr ⟩
        α .ν C.∘ M₁ inv                              ∎
```

### Univalence

The displayed category of monad algebras is a
[[displayed univalent category]]. This is relatively straightforward
to show: first, note that the type of displayed isomorphisms must
be a proposition. Next, we can perform a bit of simple algebra to show
that the actions of two isomorphic $M$-algebras are, in fact, equal.

```agda
  Monad-algebras-is-category : is-category-displayed (Monad-algebras M)
  Monad-algebras-is-category f α (β , p) (γ , q) =
    Σ-prop-path (λ _ _ _ → ext prop!) $ ext $
      β .ν                         ≡⟨ C.introl invl ⟩
      (to C.∘ from) C.∘ β .ν       ≡⟨ C.pullr (p .from') ⟩
      to C.∘ α .ν C.∘ M₁ from      ≡⟨ C.pulll (q .to') ⟩
      (γ .ν C.∘ M₁ to) C.∘ M₁ from ≡⟨ MR.cancelr invl ⟩
      γ .ν                         ∎
    where
      open C._≅_ f
      open Cat.Displayed.Morphism (Monad-algebras M)
```

By [[univalence of total categories]], we can immediately deduce that
the Eilenberg-Moore category inherits univalence from the base category.

```agda
  EM-is-category : is-category C → is-category (Eilenberg-Moore M)
  EM-is-category cat =
    is-category-total (Monad-algebras M) cat Monad-algebras-is-category
```

## Free algebras {defines="free-algebra kleisli-category"}

In exactly the same way that we may construct a _[free group]_ by taking
the inhabitants of some set $X$ as generating the "words" of a group, we
can, given an object $A$ of the underlying category, build a **free
$M$-algebra** on $A$. Keeping with our interpretation of monads as
logical signatures, this is the _syntactic model_ of $M$, with a set of
"neutrals" chosen from the object $A$.

[free group]: Algebra.Group.Free.html

This construction is a lot simpler to do in generality than in any
specific case: We can always turn $A$ into an $M$-algebra by taking the
underlying object to be $M(A)$, and the algebra map to be the monadic
multiplication; The associativity and unit laws of the monad _itself_
become those of the $M$-action.

```agda
  Free-EM : Functor C (Eilenberg-Moore M)
  Free-EM .F₀ A .fst = M₀ A
  Free-EM .F₀ A .snd .ν = μ A
  Free-EM .F₀ A .snd .ν-mult = sym μ-assoc
  Free-EM .F₀ A .snd .ν-unit = μ-unitl
```

The construction of free $M$-algebras is furthermore functorial on the
underlying objects; Since the monadic multiplication is a natural
transformation $M\circ M \To M$, the naturality condition (drawn below)
doubles as showing that the functorial action of $M$ can be taken as an
algebraic action:

~~~{.quiver}
\[\begin{tikzcd}
  MMA && MMB \\
  \\
  MA && MB
  \arrow["MMf", from=1-1, to=1-3]
  \arrow["Mf"', from=3-1, to=3-3]
  \arrow["{\mu_A}"', from=1-1, to=3-1]
  \arrow["{\mu_B}", from=1-3, to=3-3]
\end{tikzcd}\]
~~~

```agda
  Free-EM .F₁ f .fst = M₁ f
  Free-EM .F₁ f .snd = sym $ mult.is-natural _ _ _
  Free-EM .F-id = ext M-id
  Free-EM .F-∘ f g = ext (M-∘ f g)
```

This is a free construction in the precise sense of the word: it's the
[left adjoint] to the functor `Forget-EM`{.Agda}, so in particular it
provides a systematic, [[universal|universal-morphism]] way of mapping from $\cC$ to
$\cC^M$.

[left adjoint]: Cat.Functor.Adjoint.html

```agda
  open _⊣_

  Free-EM⊣Forget-EM : Free-EM ⊣ Forget-EM
  Free-EM⊣Forget-EM .unit =
    NT M.η M.unit.is-natural
  Free-EM⊣Forget-EM .counit =
    NT (λ x → ∫hom (x .snd .ν) (x .snd .ν-mult))
      (λ x y f → ext (sym (f .snd)))
  Free-EM⊣Forget-EM .zig = ext μ-unitr
  Free-EM⊣Forget-EM .zag {x} = x .snd .ν-unit
```

The [[full subcategory]] of free $M$-algebras is often referred to
as the **Kleisli category** of $M$.

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} {F : Functor C C} (M : Monad-on F) where
  private
    module C = Cat.Reasoning C
    module M = Monad-on M
    module MR = Cat.Functor.Reasoning F
  open M
  open Algebra-on

```
-->

```agda
  Kleisli : Precategory (o ⊔ ℓ) ℓ
  Kleisli = Essential-image (Free-EM {M = M})
```

If $\cC$ is univalent then so is the Kleisli category as it is a
full subcategory of a univalent category.

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} {F : Functor C C} {M : Monad-on F} where
  private
    module C = Cat.Reasoning C
    module M = Monad-on M
    module MR = Cat.Functor.Reasoning F
  open Algebra-on
  open M
```
-->

```agda
  Kleisli-is-category : is-category C → is-category (Kleisli M)
  Kleisli-is-category cat = Essential-image-is-category Free-EM
    (EM-is-category cat)
```

As the Kleisli category is a full subcategory, there is a canonical
full inclusion into the Eilenberg-Moore category.

```agda
  Kleisli→EM : Functor (Kleisli M) (Eilenberg-Moore M)
  Kleisli→EM = Forget-full-subcat

  Kleisli→EM-is-ff : is-fully-faithful Kleisli→EM
  Kleisli→EM-is-ff = id-equiv
```

Additionally, the free/forgetful adjunction between $\cC$ and the
Eilenberg-Moore category can be restricted to the Kleisli category.

```agda
  Forget-Kleisli : Functor (Kleisli M) C
  Forget-Kleisli = Forget-EM F∘ Kleisli→EM

  Free-Kleisli : Functor C (Kleisli M)
  Free-Kleisli = Essential-inc Free-EM

  Free-Kleisli⊣Forget-Kleisli : Free-Kleisli ⊣ Forget-Kleisli
  Free-Kleisli⊣Forget-Kleisli ._⊣_.unit ._=>_.η = η
  Free-Kleisli⊣Forget-Kleisli ._⊣_.unit .is-natural = unit.is-natural
  Free-Kleisli⊣Forget-Kleisli ._⊣_.counit ._=>_.η ((X , α) , free) =
    ∫hom (α .ν) (α .ν-mult)
  Free-Kleisli⊣Forget-Kleisli ._⊣_.counit .is-natural _ _ f =
    ext (sym (f .snd))
  Free-Kleisli⊣Forget-Kleisli ._⊣_.zig = ext μ-unitr
  Free-Kleisli⊣Forget-Kleisli ._⊣_.zag {(X , α) , free} =
    α . ν-unit
```

Note that the forgetful functor from the Kleisli category of $M$
to $\cC$ is also faithful and conservative.

```agda
  Forget-Kleisli-is-faithful : is-faithful Forget-Kleisli
  Forget-Kleisli-is-faithful = Forget-EM-is-faithful

  Forget-Kleisli-is-conservative : is-conservative Forget-Kleisli
  Forget-Kleisli-is-conservative f-inv =
    super-inv→sub-inv _ $
    Forget-EM-is-conservative f-inv
```


<!--
```agda
module _ {o h : _} {C : Precategory o h} {F G : Functor C C} {M : Monad-on F} {N : Monad-on G} where
  private
    module C = Cat.Reasoning C
    module M = Monad-on M
    module N = Monad-on N
    unquoteDecl eqv = declare-record-iso eqv (quote Monad-on)

  Monad-on-path
    : (p0 : F ≡ G)
    → (∀ x → PathP (λ i → C.Hom x (p0 i · x)) (M.η x) (N.η x))
    → (∀ x → PathP (λ i → C.Hom (p0 i · (p0 i · x)) (p0 i · x)) (M.μ x) (N.μ x))
    → PathP (λ i → Monad-on (p0 i)) M N
  Monad-on-path M=N punit pmult = injectiveP (λ _ → eqv) $
    Nat-pathp refl M=N punit ,ₚ Nat-pathp (ap₂ _F∘_ M=N M=N) M=N pmult ,ₚ prop!
```
-->
