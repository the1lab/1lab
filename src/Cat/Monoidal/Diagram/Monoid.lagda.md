<!--
```agda
open import Algebra.Monoid using (is-monoid)

open import Cat.Monoidal.Instances.Cartesian
open import Cat.Displayed.Univalence.Thin
open import Cat.Displayed.Functor
open import Cat.Bi.Diagram.Monad
open import Cat.Monoidal.Functor
open import Cat.Displayed.Base
open import Cat.Displayed.Path
open import Cat.Monoidal.Base
open import Cat.Bi.Base
open import Cat.Prelude

import Algebra.Monoid.Category as Mon
import Algebra.Monoid as Mon

import Cat.Functor.Reasoning
import Cat.Diagram.Monad as Mo
import Cat.Reasoning

open is-monoid
```
-->

```agda
module Cat.Monoidal.Diagram.Monoid where
```

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} (M : Monoidal-category C) where
  private module C where
    open Cat.Reasoning C public
    open Monoidal-category M public
```
-->

# Monoids in a monoidal category

Let $(\cC, \otimes, 1)$ be a [monoidal category] you want to study.
It can be, for instance, one of the [endomorphism categories] in a
[[bicategory]] that you like. A **monoid object in $\cC$**, generally
just called a "monoid in $\cC$", is really a collection of diagrams
in $\cC$ centered around an object $M$, the monoid itself.

[monoidal category]: Cat.Monoidal.Base.html#monoidal-categories
[endomorphism categories]: Cat.Monoidal.Base.html#endomorphism-categories

In addition to the object, we also require a "unit" map $\eta : 1 \to M$
and "multiplication" map $\mu : M \otimes M \to M$. Moreover, these maps
should be compatible with the unitors and associator of the underlying
monoidal category:

```agda
  record Monoid-on (M : C.Ob) : Type ℓ where
    no-eta-equality
    field
      η : C.Hom C.Unit M
      μ : C.Hom (M C.⊗ M) M

      μ-unitl : μ C.∘ (η C.◀ _) ≡ C.λ← _
      μ-unitr : μ C.∘ (_ C.▶ η) ≡ C.ρ← _
      μ-assoc : μ C.∘ (_ C.▶ μ) ≡ μ C.∘ (μ C.◀ _) C.∘ C.α← _
```

If we think of $\cC$ as a bicategory with a single object $*$ ---
that is, we _deloop_ it ---, then a monoid in $\cC$ is given by
precisely the same data as a monad in $\bf{B}\cC$, on the object $*$.

<!--
```agda
  private
    BC = Deloop M
    module BC = Prebicategory BC
  open Monoid-on

  Monoid-pathp
    : ∀ {P : I → C.Ob} {x : Monoid-on (P i0)} {y : Monoid-on (P i1)}
    → PathP (λ i → C.Hom C.Unit (P i)) (x .η) (y .η)
    → PathP (λ i → C.Hom (P i C.⊗ P i) (P i)) (x .μ) (y .μ)
    → PathP (λ i → Monoid-on (P i)) x y
  Monoid-pathp {x = x} {y} p q i .η = p i
  Monoid-pathp {x = x} {y} p q i .μ = q i
  Monoid-pathp {P = P} {x} {y} p q i .μ-unitl =
    is-prop→pathp
      (λ i → C.Hom-set _ (P i) (q i C.∘ (p i C.◀ _)) (C.λ← _))
      (x .μ-unitl)
      (y .μ-unitl)
      i
  Monoid-pathp {P = P} {x} {y} p q i .μ-unitr =
    is-prop→pathp
      (λ i → C.Hom-set _ (P i) (q i C.∘ (_ C.▶ p i)) (C.ρ← _))
      (x .μ-unitr)
      (y .μ-unitr)
      i
  Monoid-pathp {P = P} {x} {y} p q i .μ-assoc =
    is-prop→pathp
      (λ i → C.Hom-set _ (P i)
        (q i C.∘ (_ C.▶ q i))
        (q i C.∘ (q i C.◀ _) C.∘ C.α← _))
      (x .μ-assoc)
      (y .μ-assoc)
      i
```
-->

```agda
  monad→monoid : (M : Monad BC tt) → Monoid-on (M .Monad.M)
  monad→monoid M = go where
    module M = Monad M
    go : Monoid-on M.M
    go .η = M.η
    go .μ = M.μ
    go .μ-unitl = M.μ-unitl
    go .μ-unitr = M.μ-unitr
    go .μ-assoc = M.μ-assoc

  monoid→monad : ∀ {M} → Monoid-on M → Monad BC tt
  monoid→monad M = go where
    module M = Monoid-on M
    go : Monad BC tt
    go .Monad.M = _
    go .Monad.μ = M.μ
    go .Monad.η = M.η
    go .Monad.μ-assoc = M.μ-assoc
    go .Monad.μ-unitr = M.μ-unitr
    go .Monad.μ-unitl = M.μ-unitl
```

Put another way, a monad is just a monoid in the category of
~~endofunctors~~ endo-1-cells, what's the problem?

## The category Mon(C)

The monoid objects in $\cC$ can be made into a category, much like the
[monoids in the category of sets]. In fact, we shall see later that when
$\Sets$ is equipped with its [Cartesian monoidal structure],
$\rm{Mon}(\Sets) \cong \rm{Mon}$. Rather than defining $\rm{Mon}(\cC)$
directly as a category, we instead define it as a category
$\rm{Mon}(\cC) \liesover \cC$ [[displayed over|displayed category]]
$\cC$, which fits naturally with the way we have defined
`Monoid-object-on`{.Agda}.

[Cartesian monoidal structure]: Cat.Monoidal.Instances.Cartesian.html
[monoids in the category of sets]: Algebra.Monoid.html

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} (M : Monoidal-category C) where
  private module C where
    open Cat.Reasoning C public
    open Monoidal-category M public
```
-->

Therefore, rather than defining a type of monoid homomorphisms, we
define a predicate on maps $f : m \to n$ expressing the condition of
being a monoid homomorphism. This is the familiar condition from
algebra, but expressed in a point-free way:

```agda
  record
    is-monoid-hom {m n} (f : C.Hom m n)
     (mo : Monoid-on M m) (no : Monoid-on M n) : Type ℓ where

    private
      module m = Monoid-on mo
      module n = Monoid-on no

    field
      pres-η : f C.∘ m.η ≡ n.η
      pres-μ : f C.∘ m.μ ≡ n.μ C.∘ (f C.⊗₁ f)
```

Since being a monoid homomorphism is a pair of propositions, the overall
condition is a proposition as well. This means that we will not need to
concern ourselves with proving displayed identity and associativity
laws, a great simplification.

<!--
```agda
  private
    unquoteDecl eqv = declare-record-iso eqv (quote is-monoid-hom)

    instance
      H-Level-is-monoid-hom : ∀ {m n} {f : C .Precategory.Hom m n} {mo no} {k} → H-Level (is-monoid-hom f mo no) (suc k)
      H-Level-is-monoid-hom = prop-instance $ Iso→is-hlevel! 1 eqv

  open Displayed
  open Functor
  open is-monoid-hom
```
-->

```agda
  Mon[_] : Displayed C ℓ ℓ
  Mon[_] = with-thin-display record where
    Ob[_]  = Monoid-on M
    Hom[_] = is-monoid-hom
```

The most complicated step of putting together the displayed category of
monoid objects is proving that monoid homomorphisms are closed under
composition. However, even in the point-free setting of an arbitrary
category $\cC$, the reasoning isn't _that_ painful:

```agda
    id' = record where
      pres-η = C.idl _
      pres-μ = C.idl _ ∙ C.intror C.⊗.F-id

    _∘'_ {x = x} {y} {z} {f} {g} fh gh = record where
      pres-η = C.pullr (gh .pres-η) ∙ fh .pres-η
      pres-μ =
        (f C.∘ g) C.∘ x .Monoid-on.μ                ≡⟨ C.pullr (gh .pres-μ) ⟩
        f C.∘ y .Monoid-on.μ C.∘ (g C.⊗₁ g)         ≡⟨ C.extendl (fh .pres-μ) ⟩
        Monoid-on.μ z C.∘ (f C.⊗₁ f) C.∘ (g C.⊗₁ g) ≡˘⟨ C.refl⟩∘⟨ C.⊗.F-∘ _ _ ⟩
        Monoid-on.μ z C.∘ (f C.∘ g C.⊗₁ f C.∘ g)    ∎
```

<!--
```agda
unquoteDecl H-Level-is-monoid-hom = declare-record-hlevel 1 H-Level-is-monoid-hom (quote is-monoid-hom)

private
  Mon : ∀ {ℓ} → Displayed (Sets ℓ) _ _
  Mon = Thin-structure-over (Mon.Monoid-structure _)
```
-->

Constructing this displayed category for the Cartesian monoidal
structure on the category of sets, we find that it is but a few
renamings away from the ordinary category of monoids-on-sets. The only
thing out of the ordinary about the proof below is that we can establish
the _displayed categories_ themselves are identical, so it is a trivial
step to show they induce identical^[thus isomorphic, thus equivalent]
[[total categories]].

```agda
Mon[Sets]≡Mon : ∀ {ℓ} → Mon[ Setsₓ ] ≡ Mon {ℓ}
Mon[Sets]≡Mon {ℓ} = Displayed-path F (λ a → is-iso→is-equiv (fiso a)) ff where
  open Displayed-functor
  open Monoid-on
  open is-monoid-hom

  open Mon.Monoid-hom
  open Mon.Monoid-on
```

The construction proceeds in three steps: First, put together a functor
([[displayed over|displayed functor]] the identity) $\rm{Mon}(\cC) \to
\thecat{Mon}$; Then,
prove that its action on objects ("step 2") and action on morphisms
("step 3") are independently equivalences of types. The characterisation
of paths of displayed categories will take care of turning this data
into an identification.

```agda
  F : Vertical-functor Mon[ Setsₓ ] Mon
  F .F₀' o .identity = o .η (lift tt)
  F .F₀' o ._⋆_ x y = o .μ (x , y)
  F .F₀' o .has-is-monoid .has-is-semigroup =
    record { has-is-magma = record { has-is-set = hlevel 2 }
           ; associative  = o .μ-assoc $ₚ _
           }
  F .F₀' o .has-is-monoid .idl = o .μ-unitl $ₚ _
  F .F₀' o .has-is-monoid .idr = o .μ-unitr $ₚ _
  F .F₁' wit .pres-id = wit .pres-η $ₚ _
  F .F₁' wit .pres-⋆ x y = wit .pres-μ $ₚ _
  F .F-id' = prop!
  F .F-∘' = prop!

  open is-iso

  fiso : ∀ a → is-iso (F .F₀' {a})
  fiso T .from m .η _ = m .identity
  fiso T .from m .μ (a , b) = m ._⋆_ a b
  fiso T .from m .μ-unitl = funext λ _ → m .idl
  fiso T .from m .μ-unitr = funext λ _ → m .idr
  fiso T .from m .μ-assoc = funext λ _ → m .associative
  fiso T .rinv x = Mon.Monoid-structure _ .id-hom-unique
    (record { pres-id = refl ; pres-⋆ = λ _ _ → refl })
    (record { pres-id = refl ; pres-⋆ = λ _ _ → refl })
  fiso T .linv m = Monoid-pathp Setsₓ refl refl

  ff : ∀ {a b : Set _} {f : ∣ a ∣ → ∣ b ∣} {a' b'}
     → is-equiv (F₁' F {a} {b} {f} {a'} {b'})
  ff {a} {b} {f} {a'} {b'} = biimp-is-equiv! (λ z → F₁' F z) invs where
    invs : Mon.Monoid-hom (F .F₀' a') (F .F₀' b') f → is-monoid-hom Setsₓ f a' b'
    invs m .pres-η = funext λ _ → m .pres-id
    invs m .pres-μ = funext λ _ → m .pres-⋆ _ _
```

## Monoidal functors preserve monoids

<!--
```agda
module _ {oc ℓc od ℓd}
  {C : Precategory oc ℓc} {D : Precategory od ℓd}
  {MC : Monoidal-category C} {MD : Monoidal-category D}
  ((F , MF) : Lax-monoidal-functor MC MD)
  where
  private module C where
    open Cat.Reasoning C public
    open Monoidal-category MC public
  open Cat.Reasoning D
  open Monoidal-category MD

  open Functor F
  private module F = Cat.Functor.Reasoning F
  open Lax-monoidal-functor-on MF

  open Displayed-functor
  open Monoid-on
  open is-monoid-hom
```
-->

If $F$ is a [[lax monoidal functor]] between monoidal categories $\cC$
and $\cD$, and $M$ is a monoid in $\cC$, then $FM$ can be equipped with
the structure of a monoid in $\cC$.

We can phrase this nicely as a [[displayed functor]] $\rm{Mon}_1(F) :
\rm{Mon}(\cC) \to \rm{Mon}(\cD)$ over $F$:

```agda
  Mon₁[_] : Displayed-functor F Mon[ MC ] Mon[ MD ]
  Mon₁[_] .F₀' m .η = F₁ (m .η) ∘ ε
  Mon₁[_] .F₀' m .μ = F₁ (m .μ) ∘ φ
```

The unit laws are witnessed by the commutativity of this diagram:

~~~{.quiver}
\[\begin{tikzcd}
  {1\otimes FX} && FX && {FX \otimes 1} \\
  & {F(1\otimes X)} & {F(X\otimes X)} & {F(X \otimes 1)} \\
  {F1\otimes FX} && {FX \otimes FX} && {FX \otimes F1}
  \arrow["{\epsilon\otimes FX}"', from=1-1, to=3-1]
  \arrow["\lambda", from=1-1, to=1-3]
  \arrow["{F\eta\otimes FX}"', from=3-1, to=3-3]
  \arrow["\varphi"{description}, from=3-3, to=2-3]
  \arrow["F\mu"{description}, from=2-3, to=1-3]
  \arrow["\varphi", from=3-1, to=2-2]
  \arrow["{F(\eta\otimes X)}"', from=2-2, to=2-3]
  \arrow["F\lambda", from=2-2, to=1-3]
  \arrow["F\rho"', from=2-4, to=1-3]
  \arrow["{F(X \otimes \eta)}", from=2-4, to=2-3]
  \arrow["{FX \otimes F\eta}", from=3-5, to=3-3]
  \arrow["\varphi"', from=3-5, to=2-4]
  \arrow["{FX \otimes \epsilon}", from=1-5, to=3-5]
  \arrow["\rho"', from=1-5, to=1-3]
\end{tikzcd}\]
~~~

```agda
  Mon₁[_] .F₀' m .μ-unitl =
    (F₁ (m .μ) ∘ φ) ∘ ((F₁ (m .η) ∘ ε) ◀ _)    ≡⟨ pullr (refl⟩∘⟨ ◀.expand refl) ⟩
    F₁ (m .μ) ∘ φ ∘ (F₁ (m .η) ◀ _) ∘ (ε ◀ _)  ≡⟨ refl⟩∘⟨ extendl φ.natural-◀ ⟩
    F₁ (m .μ) ∘ F₁ (m .η C.◀ _) ∘ φ ∘ (ε ◀ _)  ≡⟨ F.pulll (m .μ-unitl) ⟩
    F₁ (C.λ← _) ∘ φ ∘ (ε ◀ _)                  ≡⟨ F-λ← ⟩
    λ← _                                       ∎
  Mon₁[_] .F₀' m .μ-unitr =
    (F₁ (m .μ) ∘ φ) ∘ (_ ▶ (F₁ (m .η) ∘ ε))   ≡⟨ pullr (refl⟩∘⟨ ▶.expand refl) ⟩
    F₁ (m .μ) ∘ φ ∘ (_ ▶ F₁ (m .η)) ∘ (_ ▶ ε) ≡⟨ refl⟩∘⟨ extendl φ.natural-▶ ⟩
    F₁ (m .μ) ∘ F₁ (_ C.▶ m .η) ∘ φ ∘ (_ ▶ ε) ≡⟨ F.pulll (m .μ-unitr) ⟩
    F₁ (C.ρ← _) ∘ φ ∘ (_ ▶ ε)                 ≡⟨ F-ρ← ⟩
    ρ← _                                      ∎
```

... and the associativity by this one.

~~~{.quiver}
\[\begin{tikzcd}
  {FX \otimes (FX \otimes FX)} & {FX \otimes F(X \otimes X)} & {FX \otimes FX} \\
  & {F(X \otimes (X \otimes X))} & {F(X \otimes X)} \\
  && FX \\
  & {F((X \otimes X) \otimes X)} & {F(X \otimes X)} \\
  {(FX \otimes FX) \otimes FX} & {F(X \otimes X) \otimes FX} & {FX \otimes FX}
  \arrow["{FX \otimes \varphi}", from=1-1, to=1-2]
  \arrow["{FX \otimes F\mu}", from=1-2, to=1-3]
  \arrow["\varphi", from=1-3, to=2-3]
  \arrow["F\mu", from=2-3, to=3-3]
  \arrow["{\alpha^{-1}}"', from=1-1, to=5-1]
  \arrow["{\varphi\otimes FX}"', from=5-1, to=5-2]
  \arrow["{F\mu \otimes FX}"', from=5-2, to=5-3]
  \arrow["\varphi"', from=5-3, to=4-3]
  \arrow["F\mu"', from=4-3, to=3-3]
  \arrow["\varphi"', from=1-2, to=2-2]
  \arrow["\varphi", from=5-2, to=4-2]
  \arrow["{F\alpha^{-1}}"', from=2-2, to=4-2]
  \arrow["{F(X \otimes \mu)}", from=2-2, to=2-3]
  \arrow["{F(\mu \otimes X)}"', from=4-2, to=4-3]
\end{tikzcd}\]
~~~

```agda
  Mon₁[_] .F₀' m .μ-assoc =
    (F₁ (m .μ) ∘ φ) ∘ (_ ▶ F₁ (m .μ) ∘ φ)                ≡⟨ pullr (refl⟩∘⟨ ▶.expand refl) ⟩
    F₁ (m .μ) ∘ φ ∘ (_ ▶ F₁ (m .μ)) ∘ (_ ▶ φ)            ≡⟨ extend-inner φ.natural-▶ ⟩
    F₁ (m .μ) ∘ F₁ (_ C.▶ μ m) ∘ φ ∘ (_ ▶ φ)             ≡⟨ F.pulll (m .μ-assoc) ⟩
    F₁ (μ m C.∘ (μ m C.◀ _) C.∘ C.α← _) ∘ φ ∘ (_ ▶ φ)    ≡⟨ F.popr (F.popr F-α←) ⟩
    (F.F₁ (μ m) ∘ F.F₁ (μ m C.◀ _) ∘ φ ∘ (φ ◀ _) ∘ α← _) ≡˘⟨ pullr (extendl φ.natural-◀) ⟩
    (F.F₁ (μ m) ∘ φ) ∘ (F₁ (μ m) ◀ _) ∘ (φ ◀ _) ∘ α← _   ≡⟨ refl⟩∘⟨ ◀.pulll refl ⟩
    (F₁ (m .μ) ∘ φ) ∘ ((F₁ (m .μ) ∘ φ) ◀ _) ∘ α← _       ∎
```

Functoriality for $\rm{Mon}_1(-)$ means that, given a monoid homomorphism
$f : M \to N$, the map $Ff : FM \to FN$ is a monoid homomorphism
between the induced monoids on $FM$ and $FN$.

```agda
  Mon₁[_] .F₁' h .pres-η = F.pulll (h .pres-η)
  Mon₁[_] .F₁' h .pres-μ = F.extendl (h .pres-μ) ∙ pushr
    (F.popr (sym φ.natural-▶) ∙ extendl (sym φ.natural-◀))
  Mon₁[_] .F-id' = prop!
  Mon₁[_] .F-∘' = prop!
```
