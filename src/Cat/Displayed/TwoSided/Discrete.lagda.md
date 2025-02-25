---
description: |
  Discrete two-sided fibrations.
---
<!--
```agda
open import Cat.Displayed.Cocartesian
open import Cat.Displayed.Cartesian
open import Cat.Displayed.TwoSided
open import Cat.Instances.Product
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning
import Cat.Displayed.Morphism
import Cat.Reasoning
```
-->

```agda
module Cat.Displayed.TwoSided.Discrete where
```

# Discrete two-sided fibrations

Much like how [[discrete fibrations are presheaves]], a **discrete two-sided
fibration** is a displayed presentation of a profunctor.

:::{.definition #discrete-two-sided-fibration}
A [[displayed category]] $\cE \liesover \cA \times \cB$ is a **discrete two-sided
fibration** if:

<!--
```agda
module _
  {oa ℓa ob ℓb oe ℓe}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  (E : Displayed (A ×ᶜ B) oe ℓe)
  where
  private
    module A = Cat.Reasoning A
    module B = Cat.Reasoning B
    module A×B = Cat.Reasoning (A ×ᶜ B)
    open Cat.Displayed.Reasoning E
    open Cat.Displayed.Morphism E
    open Displayed E
```
-->

```agda
  record is-discrete-two-sided-fibration : Type (oa ⊔ ℓa ⊔ ob ⊔ ℓb ⊔ oe ⊔ ℓe) where
```

1. For every $A : \cA$, $B : \cB$, the type $\cE_{A, B}$ is a [[set]].

```agda
    field
      fibre-set : ∀ a b → is-set (Ob[ a , b ])
```

2. For every $u : \cA(A_1, A_2)$ and $Y : \cE_{A_2, B}$, there exists a
unique pair $u^{*}, \pi_{u,Y}$ that fit into the diagram below.

~~~{.quiver}
\begin{tikzcd}
  {u^*(Y)} && Y \\
  \\
  {(A_1,B)} && {(A_2,B)}
  \arrow["{\pi_{u,Y}}", dashed, lies over, from=1-1, to=1-3]
  \arrow[dashed, from=1-1, to=3-1]
  \arrow[from=1-3, lies over, to=3-3]
  \arrow["{(u,\id)}"', from=3-1, to=3-3]
\end{tikzcd}
~~~

This condition provides us with a source of [[cartesian lifts]], and
ensures that the [[pullback|pullback-fibration]] of $\cE$ along the functor
$(-,B) : \cA \to \cA \times \cB$ is a [[discrete fibration]]
for every $B : \cB$. In more intuitive terms, this means that $\cE$ is
a sort of "presheaf in $\cA$", as we can contravariantly reindex along
morphisms in $\cA$!

```agda
    field
      cart-lift
        : ∀ {a₁ a₂ : A.Ob} {b : B.Ob}
        → (f : A.Hom a₁ a₂)
        → (y' : Ob[ a₂ , b ])
        → is-contr (Σ[ x' ∈ Ob[ a₁ , b ] ] Hom[ f , B.id ] x' y')
```

<!--
```agda
    _^*_ : ∀ {a₁ a₂ : A.Ob} {b : B.Ob} → A.Hom a₁ a₂ → Ob[ a₂ , b ] → Ob[ a₁ , b ]
    u ^* y' = cart-lift u y' .centre .fst

    π*
      : ∀ {a₁ a₂ : A.Ob} {b : B.Ob}
      → (u : A.Hom a₁ a₂)
      → (y' : Ob[ a₂ , b ])
      → Hom[ u , B.id ] (u ^* y') y'
    π* u y' = cart-lift u y' .centre .snd
```
-->

3. For every $v : \cB(B_1, B_2)$ and $X : \cE_{A, B_1}$, there exists a
unique pair $v_{!}(X), \iota_{v,X}$ that fit into the following diagram.

~~~{.quiver}
\begin{tikzcd}
  X && {v_{!}(X)} \\
  \\
  {(A,B_1)} && {(A,B_2)}
  \arrow["{\iota_{v,X}}", dashed, from=1-1, to=1-3]
  \arrow[from=1-1, to=3-1]
  \arrow[dashed, from=1-3, to=3-3]
  \arrow["{(\id,v)}"', from=3-1, to=3-3]
\end{tikzcd}
~~~

This gives us a source of [[cocartesian lifts]], and ensures that
the [[pullback|pullback-fibration]] of $\cE$ along the functor
$(A,-) : \cB \to \cA \times \cB$ is a discrete opfibration.

```agda
    field
      cocart-lift
        : ∀ {a : A.Ob} {b₁ b₂ : B.Ob}
        → (f : B.Hom b₁ b₂)
        → (x' : Ob[ a , b₁ ])
        → is-contr (Σ[ y' ∈ Ob[ a , b₂ ] ] Hom[ A.id , f ] x' y')
```

<!--
```agda
    _^!_ : ∀ {a : A.Ob} {b₁ b₂ : B.Ob} → B.Hom b₁ b₂ → Ob[ a , b₁ ] → Ob[ a , b₂ ]
    v ^! x' = cocart-lift v x' .centre .fst

    ι!
      : ∀ {a : A.Ob} {b₁ b₂ : B.Ob}
      → (v : B.Hom b₁ b₂)
      → (x' : Ob[ a , b₁ ])
      → Hom[ A.id , v ] x' (v ^! x')
    ι! v x' = cocart-lift v x' .centre .snd
```
-->


4. For every $f : \cE_{u, v}(X,Y)$, there exists a vertical map
  $\alpha_{f} : \cE_{\id, \id}(v_{!}(X), u^{*}(Y))$ that causes
  the following diagram to commute.

~~~{.quiver}
\begin{tikzcd}
	& {v_{!}(X)} &&& {u^{*}(Y)} \\
	X &&& Y \\
	& {(A_1,B_2)} &&& {(A_1,B_2)} \\
	{(A_1,B_1)} &&& {(A_2,B_2)}
	\arrow["{\alpha_f}", dashed, from=1-2, to=1-5]
	\arrow[from=1-2, lies over, to=3-2]
	\arrow["{\pi_{u,Y}}"'{pos=0.7}, from=1-5, to=2-4]
	\arrow[from=1-5, lies over, to=3-5]
	\arrow["{\iota_{v,X}}"{pos=0.3}, from=2-1, to=1-2]
	\arrow["f", from=2-1, to=2-4]
	\arrow[from=2-1, lies over, to=4-1]
	\arrow[from=2-4, lies over, to=4-4]
	\arrow["{(\id,\id)}", from=3-2, to=3-5]
	\arrow["{(u,\id)}", from=3-5, to=4-4]
	\arrow["{(\id,v)}", from=4-1, to=3-2]
	\arrow["{(u,v)}"', from=4-1, to=4-4]
\end{tikzcd}
~~~

This condition is a bit opaque, and is best understood from the indexed
point of view. From this perspective, our previous 2 conditions ensure
that $\cE$ is *separately* functorial in $\cA\op$ and $\cB$; there is
no way to commute the two reindexing functors! To get something that is
*jointly* functorial, we need to assert the existence of some extra lifts
that allow us more room to manuever.

```agda
    field
      vert-lift
        : ∀ {a₁ a₂ b₁ b₂ x y}
        → {u : A.Hom a₁ a₂} {v : B.Hom b₁ b₂}
        → (f : Hom[ u , v ] x y)
        → Hom[ A.id , B.id ] (v ^! x) (u ^* y)

      factors
        : ∀ {a₁ a₂ b₁ b₂ x y}
        → {u : A.Hom a₁ a₂} {v : B.Hom b₁ b₂}
        → (f : Hom[ u , v ] x y)
        → f ≡[ A.intror (A.idl _) ,ₚ B.insertl (B.idl _) ] (π* u y ∘' vert-lift f ∘' ι! v x)
```
:::

In particular, the existence of such vertical lifts ensure that the for
every $f : \cE_{u,v}(X,Y)$, the lifts $u^{*}(Y)$ and $v_{!}(X)$ coincide.

```agda
    same-lift
      : ∀ {a₁ a₂ b₁ b₂ x' y'} {u : A.Hom a₁ a₂} {v : B.Hom b₁ b₂}
      → (f : Hom[ u , v ] x' y')
      → u ^* y' ≡ v ^! x'
```

First, note that it suffices to construct a map $\cE_{\id,\id}(v_{!}(X), u^{*}(Y))$,
as the space of lifts of $u^{*}(Y)$ along $\id$ is contractible. The above
axiom ensures that this map exists!

```agda
    same-lift {x' = x'} {y' = y'} {u = u} {v = v} f =
       ap fst $ is-contr→is-prop (cart-lift A.id (u ^* y'))
         (u ^* y' , id')
         (v ^! x' , vert-lift f)
```

Moreover, the factorisation condition ensures that every hom set forms
a [[proposition]].

```agda
    Hom[]-is-prop
      : ∀ {a₁ a₂ b₁ b₂ x' y'} {u : A.Hom a₁ a₂} {v : B.Hom b₁ b₂}
      → is-prop (Hom[ u , v ] x' y')
```

Let $f, g : \cE_{u,v}(X,Y)$ be a pair of morphisms. Both maps factor
as $\pi_{u,Y} \circ \alpha_{f} \circ \iota_{v,X}$ and
$\pi_{u,Y} \circ \alpha_{g} \circ \iota_{v,X}$, so it suffices to
show that $\alpha_{f} = \alpha_{g}$.

```agda
    Hom[]-is-prop {x' = x'} {y' = y'} {u = u} {v = v} f' g' =
      cast[] $
        f'                                     ≡[]⟨ factors f' ⟩
        π* u y' ∘' ⌜ vert-lift f' ⌝ ∘' ι! v x' ≡[]⟨ ap! vert-lift-eq ⟩
        π* u y' ∘' vert-lift g' ∘' ι! v x'     ≡[]˘⟨ factors g' ⟩
        g'                                     ∎
```

The type of objects is a set, so it further suffices to prove that
$(v_{!}(X), \alpha_{f}) = (v_{!}(X), \alpha_{g})$, which follows immediately
from uniqueness of lifts.

```agda
      where
        vert-lift-eq : vert-lift f' ≡ vert-lift g'
        vert-lift-eq =
          Σ-inj-set (fibre-set _ _) $
          is-contr→is-prop (cart-lift A.id (u ^* y'))
            (v ^! x' , vert-lift f')
            (v ^! x' , vert-lift g')
```

An alternative view is that these final conditions ensure that morphisms
$\cE_{u, v}(X,Y)$ are equivalent to proofs that $u^{*}(Y) = v_{!}(X)$.

```agda
    opaque
      discrete-two-sided-hom
        : ∀ {a₁ a₂ b₁ b₂ x' y'}
        → (u : A.Hom a₁ a₂) (v : B.Hom b₁ b₂)
        → (u ^* y') ≡ (v ^! x')
        → Hom[ u , v ] x' y'
      discrete-two-sided-hom {x' = x'} {y' = y'} u v p =
        hom[ A.elimr (A.idr _) ,ₚ B.cancell (B.idl _) ] $
          π* u y' ∘' subst (λ v!x → Hom[ A.id , B.id ] v!x (u ^* y')) p id' ∘' ι! v x'

    discrete-two-sided-hom-is-equiv
      : ∀ {a₁ a₂ b₁ b₂ x' y'}
      → (u : A.Hom a₁ a₂) (v : B.Hom b₁ b₂)
      → is-equiv (discrete-two-sided-hom {x' = x'} {y' = y'} u v)
    discrete-two-sided-hom-is-equiv u v =
      is-iso→is-equiv $
      iso same-lift
        (λ _ → Hom[]-is-prop _ _)
        (λ _ → fibre-set _ _ _ _ _ _)
```

## Functoriality

Note that the action $(-)^*$ is functorial on the fibres of $E$ that
are vertical over $B$, as lifts are unique.

```agda
    ^*-∘
      : ∀ {a₁ a₂ a₃ : A.Ob} {b : B.Ob}
      → (u : A.Hom a₂ a₃) (v : A.Hom a₁ a₂)
      → (y' : Ob[ a₃ , b ])
      → (u A.∘ v) ^* y' ≡ (v ^* (u ^* y'))
    ^*-∘ u v y' =
      ap fst $ cart-lift (u A.∘ v) y' .paths $
        v ^* (u ^* y') ,
        hom[ refl ,ₚ B.idl _ ] (π* u y' ∘' π* v (u ^* y'))

    ^*-id
      : ∀ {a b} {x' : Ob[ a , b ]}
      → A.id ^* x' ≡ x'
    ^*-id {x' = x'} =
      ap fst $ cart-lift A.id x' .paths (x' , id')
```

Dually, the action $(-)_{!}$ is functorial on the fibres of $E$ that
are vertical over $A$.

```agda
    ^!-∘
      : ∀ {a : A.Ob} {b₁ b₂ b₃ : B.Ob}
      → (u : B.Hom b₂ b₃) (v : B.Hom b₁ b₂)
      → (x' : Ob[ a , b₁ ])
      → (u B.∘ v) ^! x' ≡ (u ^! (v ^! x'))
    ^!-∘ u v x' =
      ap fst $ cocart-lift (u B.∘ v) x' .paths $
        u ^! (v ^! x') , hom[ A.idr _ ,ₚ refl ] (ι! u (v ^! x') ∘' ι! v x')

    ^!-id
      : ∀ {a b} {x' : Ob[ a , b ]}
      → B.id ^! x' ≡ x'
    ^!-id {x' = x'} =
      ap fst $ cocart-lift B.id x' .paths (x' , id')
```

Moreover, we also have an interchange law that lets us relate
the contravariant and covariant actions on fibres.

```agda
    ^*-^!-comm
      : ∀ {a₁ a₂ : A.Ob} {b₁ b₂ : B.Ob}
      → (u : A.Hom a₁ a₂) (v : B.Hom b₁ b₂)
      → (x' : Ob[ a₂ , b₁ ])
      → (u ^* (v ^! x')) ≡ (v ^! (u ^* x'))
    ^*-^!-comm u v x' =
      same-lift (hom[ A.idl u ,ₚ B.idr v ] (ι! v x' ∘' π* u x'))
```

## Invertible maps

Every morphism in a discrete two-sided fibration living over an
invertible pair of morphisms is itself invertible.

```agda
    all-invertible[]
      : ∀ {a₁ a₂ b₁ b₂ x' y'} {u : A.Hom a₁ a₂} {v : B.Hom b₁ b₂}
      → (f : Hom[ u , v ] x' y')
      → (uv⁻¹ : A×B.is-invertible (u , v))
      → is-invertible[ uv⁻¹ ] f
```

Let $f : \cE_{u,v}(X,Y)$ be a map displayed over a pair of invertible maps
$u : \cA(A_1, A_2), v : \cB(B_1, B_2)$.

```agda
    all-invertible[] {a₁} {a₂} {b₁} {b₂} {x'} {y'} {u} {v} f uv⁻¹ = f⁻¹ where
      module uv⁻¹ = A×B.is-invertible uv⁻¹
      open is-invertible[_]

      u⁻¹ : A.Hom _ _
      u⁻¹ = uv⁻¹.inv .fst

      v⁻¹ : B.Hom _ _
      v⁻¹ = uv⁻¹.inv .snd
```

Since each of our $\rm{Hom}$-sets is a proposition, to construct an inverse
it suffices to build a map $\cE_{u^{-1}, v^{-1}}(Y, X)$. This, in turn,
reduces to showing $(u^{-1})^{*}(X) = (v^{-1})_{!}(X)$, which follows
from some tedious functoriality algebra.

```agda
      f⁻¹ : is-invertible[ uv⁻¹ ] f
      f⁻¹ .inv' =
        discrete-two-sided-hom u⁻¹ v⁻¹ $
          u⁻¹ ^* x'                    ≡˘⟨ ap (u⁻¹ ^*_) ^!-id ⟩
          u⁻¹ ^* (⌜ B.id ⌝ ^! x')      ≡⟨ ap! (sym (ap snd $ uv⁻¹.invr)) ⟩
          u⁻¹ ^* ((v⁻¹ B.∘ v) ^! x')   ≡⟨ ap (u⁻¹ ^*_) (^!-∘ v⁻¹ v x') ⟩
          u⁻¹ ^* (v⁻¹ ^! ⌜ v ^! x' ⌝)  ≡⟨ ap! (sym (same-lift f)) ⟩
          u⁻¹ ^* (v⁻¹ ^! (u ^* y'))    ≡˘⟨ ap (u⁻¹ ^*_) (^*-^!-comm u v⁻¹ y') ⟩
          u⁻¹ ^* (u ^* (v⁻¹ ^! y'))    ≡˘⟨ ^*-∘ u u⁻¹ (v⁻¹ ^! y') ⟩
          ⌜ u A.∘ u⁻¹ ⌝ ^* (v⁻¹ ^! y') ≡⟨ ap! (ap fst $ uv⁻¹.invl) ⟩
          A.id ^* (v⁻¹ ^! y')          ≡⟨ ^*-id ⟩
          v⁻¹ ^! y' ∎
      f⁻¹ .inverses' .Inverses[_].invl' =
        is-prop→pathp (λ _ → Hom[]-is-prop) _ _
      f⁻¹ .inverses' .Inverses[_].invr' =
        is-prop→pathp (λ _ → Hom[]-is-prop) _ _
```

## Cartesian and cocartesian maps

Every map that is $\cB$-vertical is [[cartesian|cartesian morphism]]; and, dually,
every map that is $\cA$-vertical is [[cocartesian|cocartesian morphism]].

```agda
    vertical-cartesian
      : ∀ {a₁ a₂ b x' y'} {u : A.Hom a₁ a₂}
      → (f : Hom[ u , B.id {b} ] x' y')
      → is-cartesian E (u , B.id) f

    vertical-cocartesian
      : ∀ {a b₁ b₂ x' y'} {v : B.Hom b₁ b₂}
      → (f : Hom[ A.id {a} , v ] x' y')
      → is-cocartesian E (A.id , v) f
```

The proof is a bit more functoriality algebra.

```agda
    vertical-cartesian {x' = x'} {y'} {u} f .is-cartesian.universal {_} {a'} (v , w) h =
      discrete-two-sided-hom v w $
        v ^* x'            ≡˘⟨ ap (v ^*_) ^!-id ⟩
        v ^* (B.id ^! x')  ≡˘⟨ ap (v ^*_) (same-lift f) ⟩
        v ^* (u ^* y')     ≡˘⟨ ^*-∘ u v y' ⟩
        (u A.∘ v) ^* y'    ≡⟨ same-lift h ⟩
        (B.id B.∘ w) ^! a' ≡⟨ ap (_^! a') (B.idl w) ⟩
        w ^! a'            ∎
    vertical-cartesian {x' = x'} {y'} {u} f .is-cartesian.commutes _ _ =
      Hom[]-is-prop _ _
    vertical-cartesian {x' = x'} {y'} {u} f .is-cartesian.unique _ _ =
      Hom[]-is-prop _ _
```

<details>
<summary>The cocartesian case is formally dual, so we omit the details.
</summary>
```agda
    vertical-cocartesian {x' = x'} {y'} {v} f .is-cocartesian.universal {_} {a'} (u , w) h =
      discrete-two-sided-hom u w $
        u ^* a'            ≡˘⟨ ap (_^* a') (A.idr _) ⟩
        (u A.∘ A.id) ^* a' ≡⟨ same-lift h ⟩
        (w B.∘ v) ^! x'    ≡⟨ ^!-∘ w v x' ⟩
        w ^! (v ^! x')     ≡˘⟨ ap (w ^!_) (same-lift f) ⟩
        w ^! (A.id ^* y')  ≡⟨ ap (w ^!_) ^*-id ⟩
        w ^! y'            ∎
    vertical-cocartesian {x' = x'} {y'} {v} f .is-cocartesian.commutes _ _ =
      Hom[]-is-prop _ _
    vertical-cocartesian {x' = x'} {y'} {v} f .is-cocartesian.unique _ _ =
      Hom[]-is-prop _ _
```
</details>

## Discrete two-sided fibrations are two-sided fibrations

<!--
```agda
module _
  {oa ℓa ob ℓb oe ℓe}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  (E : Displayed (A ×ᶜ B) oe ℓe)
  where
  private
    module A = Cat.Reasoning A
    module B = Cat.Reasoning B
    open Cat.Displayed.Reasoning E
    open Cat.Displayed.Morphism E
    open Displayed E
```
-->

Every discrete two-sided fibration is a [[two-sided fibration]].

```agda
  discrete-two-sided-fibration→two-sided-fibration
    : is-discrete-two-sided-fibration E
    → Two-sided-fibration E
```

This is essentially a triviality at this point: every $A$-vertical map
is cocartesian, and every $B$-vertical map is cartesian, and all requisite
lifts exit.

```agda
  discrete-two-sided-fibration→two-sided-fibration E-dfib = E-fib where
    open is-discrete-two-sided-fibration E-dfib
    open Two-sided-fibration
    open Cocartesian-lift
    open Cartesian-lift

    E-fib : Two-sided-fibration E
    E-fib .cart-lift u y' .x' = u ^* y'
    E-fib .cart-lift u y' .lifting = π* u y'
    E-fib .cart-lift u y' .cartesian = vertical-cartesian (π* u y')
    E-fib .cocart-lift v x' .y' = v ^! x'
    E-fib .cocart-lift v x' .lifting = ι! v x'
    E-fib .cocart-lift v x' .cocartesian = vertical-cocartesian (ι! v x')
    E-fib .cart-beck-chevalley _ _ _ _ = vertical-cartesian _
    E-fib .cocart-beck-chevalley _ _ _ _ = vertical-cocartesian _
```
