```agda
open import Cat.Functor.Equivalence.Complete
open import Cat.Functor.Conservative
open import Cat.Functor.Equivalence
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Terminal
open import Cat.Diagram.Monad
open import Cat.Prelude

import Cat.Reasoning

module Cat.Diagram.Monad.Limits {o ℓ} {C : Precategory o ℓ} {M : Monad C} where
```

<!--
```agda
private
  module EM = Cat.Reasoning (Eilenberg-Moore C M)
  module C = Cat.Reasoning C
  module M = Monad M

open Algebra-hom
open Algebra-on
open Cone-hom
open Cone
```
-->

# Limits in categories of algebras

Suppose that $\ca{C}$ be a category, $M$ be a [monad] on $\ca{C}$, and
$F$ be a $\ca{J}$-shaped diagram of [$M$-algebras][malg] (that is, a
functor $F : \ca{J} \to \ca{C}^M$ into the [Eilenberg-Moore category] of
M). Suppose that an evil wizard has given you a [limit] for the diagram
in $\ca{C}$ which underlies $F$, but they have not (being evil and all)
told you whether $\lim F$ admits an algebra structure at all.

[monad]: Cat.Diagram.Monad.html#monads
[malg]: Cat.Diagram.Monad.html#algebras-over-a-monad
[Eilenberg-Moore category]: Cat.Diagram.Monad.html#eilenberg-moore-category
[limit]: Cat.Diagram.Limit.Base.html

Perhaps we can make this situation slightly more concrete, by working in
a category _equivalent to_ an Eilenberg-Moore category: If we have two
groups $G$, $H$, considered as a discrete diagram, then the limit our
evil wizard would give us is the product $U(G) \times U(H)$ in $\sets$.
But we [already know] we can equip this product with a "pointwise" group
structure! Does this result generalise?

[already know]: Algebra.Group.Cat.FinitelyComplete.html#direct-products

The answer is positive, though this is one of those cases where abstract
nonsense can not help us: gotta roll up our sleeves and calculate away.
Suppose we have a diagram as in the setup --- we'll show that the
functor $U : \ca{C}^M \to \ca{C}$ both preserves and _reflects_ limits,
in that $K$ is a limiting cone if, and only if, $U(K)$ is.

```agda
module _ {jo jℓ} {J : Precategory jo jℓ} (F : Functor J (Eilenberg-Moore C M)) where
  private module F = Functor F

  Forget-reflects-limits
    : (K : Cone F)
    → is-limit (Forget C M F∘ F) (F-map-cone (Forget C M) K)
    → is-limit F K
  Forget-reflects-limits K uniq other = contr ! unique where
    !′ = uniq (F-map-cone (Forget C M) other) .centre
```

Let $L$ be a cone over $F$: Since $U(K)$ is a limiting cone, then we
have a unique map of $U(L) \to U(K)$, which we must show extends to a
map of _algebras_ $L \to K$, which by definition means $! \nu = \nu
M_1(!)$. But those are maps $M_0(L) \to U(K)$ --- so if $M_0(L)$ was a
cone over $U \circ F$, and those two were maps of cones, then they would
be equal!

```agda
    ! : Cone-hom _ other K
    ! .hom .morphism = !′ .hom
    ! .hom .commutes =
      ap hom $ is-contr→is-prop (uniq cone′)
        (record { hom = !′ .hom C.∘ apex other .snd .ν
                ; commutes = λ o → C.pulll (!′ .commutes o)
                })
        (record { hom = apex K .snd .ν C.∘ M.M₁ (!′ .hom)
                ; commutes = λ o → C.pulll (K .ψ o .commutes)
                                ·· C.pullr (sym (M.M-∘ _ _) ∙ ap M.M₁ (!′ .commutes o))
                                ·· sym (other .ψ o .commutes)
                })
```

The cone structure on $M_0(L)$ is given by composites $\psi_x \nu$,
which commute because $\psi$ is also a cone structure. More explicitly,
what we must show is $F_1(o) \psi_x \nu = \psi_y \nu$, which follows
immediately.

```agda
      where
        cone′ : Cone (Forget C M F∘ F)
        cone′ .apex       = M.M₀ (apex other .fst)
        cone′ .ψ x        = morphism (ψ other x) C.∘ apex other .snd .ν
        cone′ .commutes o = C.pulll (ap morphism (commutes other o))

    ! .commutes o = Algebra-hom-path _
       (uniq (F-map-cone (Forget C M) other) .centre .commutes o)
```

For uniqueness, we use that the map $U(L) \to U(K)$ is unique, and that
the functor $U$ is faithful.

```agda
    unique : ∀ x → ! ≡ x
    unique x = Cone-hom-path _ $ Algebra-hom-path _ $
      ap hom (uniq (F-map-cone (Forget _ M) other) .paths hom′)
      where
        hom′ : Cone-hom _ _ _
        hom′ .hom        = hom x .morphism
        hom′ .commutes o = ap morphism (x .commutes o)
```

I hope you like appealing to uniqueness of maps into limits, by the way.
We now relax the conditions on the theorem above, which relies on the
pre-existence of a cone $K$. In fact, what we have shown is that
`Forget` reflects the property of _being a limit_ --- what we now show
is that it reflects limit _objects_, too: if $U \circ F$ has a limit,
then so does $F$.

```agda
  Forget-lift-limit : Limit (Forget _ M F∘ F) → Limit F
  Forget-lift-limit lim-over =
    record { top = cone′
           ; has⊤ = Forget-reflects-limits cone′ $
              subst (is-limit _) (sym U$L≡L) (lim-over .has⊤)
           }
    where
      open Terminal
      module cone = Cone (lim-over .top)
```

What we must do, essentially, is prove that $\lim (U \circ F)$ admits an
algebra structure, much like we did for products of groups. In this,
we'll use two auxilliary cones over $U \circ F$, one with underlying
object given by $M(\lim (U \circ F))$ and one by $M^2(\lim (U \circ
F))$. We construct the one with a single $M$ first, and re-use its maps
in the construction of the one with $M^2$.

The maps out of $M_0(\lim (U \circ F))$ are given by the composite
below, which assembles into a cone since $F_1(f)$ is a map of algebras
and $\psi$ is a cone.

$$
M_0 (\lim (U \circ F)) \xto{M_1(\psi_x)} M_0 (F_0(x)) \xto{\nu} F_0(x)
$$

```agda
      cone₂ : Cone (Forget _ M F∘ F)
      cone₂ .apex = M.M₀ cone.apex
      cone₂ .ψ x  = F.₀ x .snd .ν C.∘ M.M₁ (cone.ψ x)
      cone₂ .commutes {x} {y} f =
        F.₁ f .morphism C.∘ F.₀ x .snd .ν C.∘ M.M₁ (cone.ψ x)           ≡⟨ C.pulll (F.₁ f .commutes) ⟩
        (F.₀ y .snd .ν C.∘ M.M₁ (F.₁ f .morphism)) C.∘ M.M₁ (cone.ψ x)  ≡⟨ C.pullr (sym (M.M-∘ _ _) ∙ ap M.M₁ (cone.commutes f)) ⟩
        F.₀ y .snd .ν C.∘ M.M₁ (cone.ψ y)                               ∎
```

Below, we can reuse the work we did above by precomposing with $M$'s
multiplication $\mu$.

```agda
      cone² : Cone (Forget _ M F∘ F)
      cone² .apex       = M.M₀ (M.M₀ cone.apex)
      cone² .ψ x        = cone₂ .ψ x C.∘ M.mult.η _
      cone² .commutes f = C.pulll (cone₂ .commutes f)
```

We now define the algebra structure on $\lim (U \circ F)$. It's very
tedious, but the multiplication is uniquely defined since it's a map
$M(\lim (U \circ F)) \to \lim (U \circ F)$ into a limit, and the
algebraic identities follow from again from limits being terminal.

```agda
      cone′ : Cone F
      cone′ .apex = cone.apex , alg where
```

<!--
```agda
        comm1 : ∀ o → _
        comm1 o =
             C.pulll (lim-over .has⊤ cone₂ .centre .commutes o)
          ·· C.pullr (sym (M.unit.is-natural _ _ _))
          ·· C.cancell (F.₀ o .snd .ν-unit)

        comm2 : ∀ o → _
        comm2 o =
             C.pulll (lim-over .has⊤ cone₂ .centre .commutes o)
          ·· C.pullr (sym (M.M-∘ _ _) ∙ ap M.M₁ (lim-over .has⊤ cone₂ .centre .commutes o) ∙ M.M-∘ _ _)
          ·· C.extendl (F.₀ o .snd .ν-mult)
          ·· ap (F.₀ o .snd .ν C.∘_) (M.mult.is-natural _ _ _) ·· C.assoc _ _ _
```
-->

```agda
        alg : Algebra-on _ M cone.apex
        alg .ν = lim-over .has⊤ cone₂ .centre .hom
        alg .ν-unit = ap hom $
          is-contr→is-prop (lim-over .has⊤ (lim-over .top))
            (record { hom = alg .ν C.∘ M.unit.η cone.apex ; commutes = comm1 })
            (record { hom = C.id ; commutes = λ _ → C.idr _ })

        alg .ν-mult = ap hom $ is-contr→is-prop (lim-over .has⊤ cone²)
          (record { hom = alg .ν C.∘ M.M₁ (alg .ν) ; commutes = comm2 })
          (record { hom      = alg .ν C.∘ M.mult.η cone.apex
                  ; commutes = λ o → C.pulll (lim-over .has⊤ cone₂ .centre .commutes o)
                  })
```

The cone maps in $\ca{C}^M$ are given by the cone maps we started with
--- specialising again to groups, we're essentially showing that the
projection map $\pi_1 : G \times H \to G$ _between sets_ is actually a
group homomorphism.

```agda
      cone′ .ψ x .morphism = cone.ψ x
      cone′ .ψ x .commutes = lim-over .has⊤ cone₂ .centre .commutes x
      cone′ .commutes f = Algebra-hom-path _ (cone.commutes f)

      U$L≡L : F-map-cone (Forget _ M) cone′ ≡ lim-over .top
      U$L≡L = Cone-path _ refl λ o → refl
```

We conclude by saying that, if $\ca{C}$ is a complete category, then so
is $\ca{C}^M$, with no assumptions on $M$.

```agda
Eilenberg-Moore-is-complete
  : ∀ {a b} → is-complete a b C → is-complete a b (Eilenberg-Moore _ M)
Eilenberg-Moore-is-complete complete F = Forget-lift-limit F (complete _)
```
