<!--
```agda
open import Cat.Prelude

open import Cat.Displayed.Base
open import Cat.Displayed.Comprehension
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Cartesian.Indexing
open import Cat.Displayed.Cocartesian
open import Cat.Displayed.Fibre
open import Cat.Displayed.Instances.Slice

import Cat.Reasoning
import Cat.Displayed.Reasoning
```
-->

```agda
module Cat.Displayed.Comprehension.Coproduct
  {o ℓ o' ℓ'} {B : Precategory o ℓ}
  {E : Displayed B o' ℓ'}
  (E-fib : Cartesian-fibration E)
  (P : Comprehension E)
  (D : Displayed B o' ℓ')
  (D-fib : Cartesian-fibration D)
  where
```

<!--
```agda
private
  open Cat.Reasoning B
  module E = Displayed E
  module D = Displayed D
  module D↓ {Γ} = Cat.Reasoning (Fibre D Γ)
  module Dr = Cat.Displayed.Reasoning D
  module D-fib {x y} (f : Hom x y) (y′ : D.Ob[ y ]) =
    Cartesian-lift (Cartesian-fibration.has-lift D-fib f y′)
  open Comprehension E E-fib P
  module D* {Γ Δ : Ob} (σ : Hom Γ Δ) = Functor (base-change D D-fib σ)
  module π* {Γ : Ob} (x : E.Ob[ Γ ]) = Functor (base-change D D-fib (πᶜ {x = x}))
  open Functor
  open _=>_
```
-->

# Coproducts in Comprehension Categories

Let $\cE$ be a [comprehension category] over $\cB$, and let $\cD$ be a
[fibration] also over $\cB$. We say that $\cD$ has $\cE$-coproducts when:
- For every $\Gamma : \cB$, $X : \cE_{\Gamma}$, and $A : \cD_{\Gamma, X}$,
there exists an object $\coprod_{X} A : \cD{\Gamma}$
- There exist cocartesian maps $\langle\rangle : A \to_{\pi} \coprod_{X} A$
in $\cD$ over projections $\Gamma, X \to X$ in $\cB$.
- For every diagram of following shape, if $f : X \to Y$ is cartesian in
$\cE$, $g$ and $h$ are cartesian in $\cD$, and $s$ is cocartesian in
$\cD$, then $r$ is cocartesian in $\cD$.

~~~{.quiver}
\begin{tikzcd}
	A &&& B \\
	&& {A'} &&& {B'} \\
	\\
	{\Gamma,X} &&& {\Delta,Y} \\
	&& \Gamma &&& \Delta
	\arrow["\pi"', from=4-1, to=5-3]
	\arrow["\pi"', from=4-4, to=5-6]
	\arrow["\sigma"', from=5-3, to=5-6]
	\arrow["{\sigma,f}"', from=4-1, to=4-4]
	\arrow[lies over, from=2-6, to=5-6]
	\arrow[lies over, from=2-3, to=5-3]
	\arrow[lies over, from=1-1, to=4-1]
	\arrow[lies over, from=1-4, to=4-4]
	\arrow["g", from=1-1, to=1-4]
	\arrow["r", from=1-1, to=2-3]
	\arrow["s", from=1-4, to=2-6]
	\arrow["h", from=2-3, to=2-6]
\end{tikzcd}
~~~      

[comprehension category]: Cat.Displayed.Comprehension.html
[fibration]: Cat.Displayed.Cartesian.html

From a type-theoretic perspective, the first two conditions are rather
straightforward. The first condition establishes that we have a type
former $\coprod$ that can quantify over objects of $\cE$. The second
condition defines an introduction rule of the following form:
$$
\frac{\Gamma, x : X \vdash a : A}{\Gamma \vdash \langle x, a \rangle : \coprod (x : X) A}
$$

Furthermore, cocartesianess of $\langle\rangle$ acts as an elimination
rule for $\coprod_{X} A$, as it gives us a means of building maps out
of it!

However, the last condition is somewhat mysterious at first glance.
What does stability of cocartesian morphisms over projections have
to do with coproducts!? Like many questions in category theory,
this can be resolved by looking at things from a type-theoretic angle.
Recall that cartesian morphisms act like substitutions; in this light,
this condition is essentially asking that the introduction form for
coproducts is stable under substitutions, which is of critical importance!

```agda
record has-comprehension-coproducts : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
  no-eta-equality
  field
    ∐ : ∀ {Γ} → (x : E.Ob[ Γ ]) (a : D.Ob[ Γ ⨾ x ]) → D.Ob[ Γ ]
    ⟨_,_⟩
      : ∀ {Γ} → (x : E.Ob[ Γ ]) (a : D.Ob[ Γ ⨾ x ])
      → D.Hom[ πᶜ ] a (∐ x a)
    ⟨⟩-cocartesian
      : ∀ {Γ} → (x : E.Ob[ Γ ]) (a : D.Ob[ Γ ⨾ x ])
      → is-cocartesian D πᶜ ⟨ x , a ⟩
    cocartesian-stable
      : ∀ {Γ Δ x y a a' b b'} {σ : Hom Γ Δ} {f : E.Hom[ σ ] x y}
      → {r : D.Hom[ πᶜ ] a a'} {h : D.Hom[ σ ] a' b'}
      → {g : D.Hom[ σ ⨾ˢ f ] a b} {s : D.Hom[ πᶜ ] b b'}
      → is-cartesian E σ f
      → s D.∘′ g D.≡[ sub-proj f ] h D.∘′ r
      → is-cocartesian D πᶜ s
      → is-cartesian D (σ ⨾ˢ f) g
      → is-cartesian D σ h
      → is-cocartesian D πᶜ r

  module ⟨⟩-cocartesian {Γ} (x : E.Ob[ Γ ]) (a : D.Ob[ Γ ⨾ x ]) =
    is-cocartesian (⟨⟩-cocartesian x a)
```

Now, some general facts about coproducts. To start, note that
coproducts are functorial.

```agda
  opaque
    ∐[_]
      : ∀ {Γ} {x : E.Ob[ Γ ]} {a b : D.Ob[ Γ ⨾ x ]}
      → D.Hom[ id ] a b → D.Hom[ id ] (∐ x a) (∐ x b)
    ∐[_] {Γ} {x} {a} {b} f =
      ⟨⟩-cocartesian.universal′ x a id-comm-sym (⟨ x , b ⟩ D.∘′ f)

    ∐[]-natural
      : ∀ {Γ} {x : E.Ob[ Γ ]} {a b : D.Ob[ Γ ⨾ x ]}
      → (f : D.Hom[ id ] a b)
      → ∐[ f ] D.∘′ ⟨ x , a ⟩ D.≡[ id-comm-sym ] ⟨ x , b ⟩ D.∘′ f
    ∐[]-natural {x = x} {a} {b} f =
      ⟨⟩-cocartesian.commutesp x a _ _

    ∐[]-id : ∀ {Γ} {x : E.Ob[ Γ ]} {a : D.Ob[ Γ ⨾ x ]} → ∐[ D.id′ {x = a} ] ≡ D.id′
    ∐[]-id {x = x} {a = a} =
      sym $ ⟨⟩-cocartesian.unique _ _ _ $ from-pathp⁻ $ Dr.cast[] $
      D.id′ D.∘′ ⟨ x , a ⟩ D.≡[]⟨ D.idl′ _ ⟩
      ⟨ x , a ⟩            D.≡[]⟨ symP (D.idr′ _ ) ⟩
      ⟨ x , a ⟩ D.∘′ D.id′ ∎
    
    ∐[]-∘
      : ∀ {Γ} {x : E.Ob[ Γ ]} {a b c : D.Ob[ Γ ⨾ x ]}
      → (f : D.Hom[ id ] b c) (g : D.Hom[ id ] a b)
      → ∐[ f D↓.∘ g ] D.≡[ sym (idl _) ] ∐[ f ] D.∘′ ∐[ g ]
    ∐[]-∘ {x = x} {a = a} {b = b} {c = c} f g =
      symP $ ⟨⟩-cocartesian.uniquep x a _ _ _ _ $
      (∐[ f ] D.∘′ ∐[ g ]) D.∘′ ⟨ x , a ⟩          D.≡[]⟨ Dr.pullr[] _ (∐[]-natural g) ⟩
      ∐[ f ] D.∘′ ⟨ x , b ⟩ D.∘′ g                 D.≡[]⟨ Dr.extendl[] _ (∐[]-natural f) ⟩
      ⟨ x , c ⟩ D.∘′ f D.∘′ g                      D.≡[]⟨ to-pathp (Dr.unwhisker-r (ap (πᶜ ∘_) (idl _)) (idl _)) ⟩
      ⟨ x , c ⟩ D.∘′ (f D↓.∘ g) ∎
```

We can construct maps out of coproducts $\coprod_{X} A \to B$ from
maps $A \to \pi^{*}(B)$. Type theoretically, this gives us an elimination
principle for coproducts!

```agda
  opaque
    ∐-elim
      : ∀ {Γ} {x : E.Ob[ Γ ]} {a : D.Ob[ Γ ⨾ x ]} {b : D.Ob[ Γ ]}
      → D.Hom[ id ] a (π*.F₀ x b)
      → D.Hom[ id ] (∐ x a) b
    ∐-elim {x = x} {a = a} {b = b} f =
      ⟨⟩-cocartesian.universal′ x a id-comm-sym (D-fib.lifting πᶜ b D.∘′ f)

    ∐-elim-β
      : ∀ {Γ} {x : E.Ob[ Γ ]} {a : D.Ob[ Γ ⨾ x ]} {b : D.Ob[ Γ ]}
      → (f : D.Hom[ id ] a (π*.F₀ x b))
      → ∐-elim f D.∘′ ⟨ x , a ⟩ D.≡[ id-comm-sym ] D-fib.lifting πᶜ b D.∘′ f
    ∐-elim-β f = ⟨⟩-cocartesian.commutesp _ _ _ _
```

Coproduct elimination is also natural. If we put on our type theory
goggles, we can see that this describes how to perform substitutions in
coproducts.

```agda
    ∐-elim-natural
      : ∀ {Γ} {x : E.Ob[ Γ ]} {a b : D.Ob[ Γ ⨾ x ]} {c : D.Ob[ Γ ]}
      → (f : D.Hom[ id ] b (π*.₀ x c)) (g : D.Hom[ id ] a b)
      → ∐-elim f D.∘′ ∐[ g ] D.≡[ idl _ ] ∐-elim (f D↓.∘ g)
    ∐-elim-natural {x = x} {a = a} {b = b} {c = c} f g =
      ⟨⟩-cocartesian.uniquep x a _ _ _ (∐-elim f D.∘′ ∐[ g ]) $
        ((∐-elim f) D.∘′ ∐[ g ]) D.∘′ ⟨ x , a ⟩     D.≡[]⟨ Dr.pullr[] _ (∐[]-natural g) ⟩
        ∐-elim f D.∘′ ⟨ x , b ⟩ D.∘′ g              D.≡[]⟨ Dr.extendl[] id-comm-sym (⟨⟩-cocartesian.commutesp x b _ _) ⟩
        D-fib.lifting πᶜ c D.∘′ f D.∘′ g            D.≡[]⟨ to-pathp (Dr.unwhisker-r (ap (πᶜ ∘_) (idl _)) (idl _)) ⟩
        D-fib.lifting πᶜ c D.∘′ Dr.hom[] (f D.∘′ g) ∎
```

Conversely, we can make maps $A \to \pi^{*}(B)$ out of maps
$\coprod_{X} A \to B$. This isn't quite as nice from a type theory
point-of-view as the elimination principle; it's a weird mash-up
of the introduction rule for coproducts, followed by reindexing.

```agda
  opaque
    ∐-transpose
      : ∀ {Γ} {x : E.Ob[ Γ ]} {a : D.Ob[ Γ ⨾ x ]} {b : D.Ob[ Γ ]}
      → D.Hom[ id ] (∐ x a) b
      → D.Hom[ id ] a (π*.₀ x b)
    ∐-transpose {x = x} {a = a} {b = b} f =
      D-fib.universal′ πᶜ b id-comm (f D.∘′ ⟨ x , a ⟩)
```

<!--
```agda
  opaque
    unfolding ∐-transpose
    ∐-transpose-weaken
        : ∀ {Γ} {x : E.Ob[ Γ ]} {a : D.Ob[ Γ ⨾ x ]} {b : D.Ob[ Γ ]}
        → (f : D.Hom[ id ] (∐ x a) b)
        → D-fib.lifting πᶜ b D.∘′ ∐-transpose f D.≡[ id-comm ] f D.∘′ ⟨ x , a ⟩
    ∐-transpose-weaken f = D-fib.commutesp πᶜ _ id-comm _
```
-->

While `∐-transpose`{.Agda} may not play an obvious type-theoretic role,
it is extremely important categorically; it is an inverse of
`∐-elim`{.Agda}!

```agda
  opaque
    unfolding ∐-elim ∐-transpose
    ∐-elim-transpose
      : ∀ {Γ} {x : E.Ob[ Γ ]} {a : D.Ob[ Γ ⨾ x ]} {b : D.Ob[ Γ ]}
      → (f : D.Hom[ id ] (∐ x a) b)
      → ∐-elim (∐-transpose f) ≡ f
    ∐-elim-transpose {x = x} {a = a} {b = b} f = sym $
      ⟨⟩-cocartesian.uniquep x a _ _ _ f $ symP $
      D-fib.commutesp πᶜ b id-comm (f D.∘′ ⟨ x , a ⟩)

    ∐-transpose-elim
      : ∀ {Γ} {x : E.Ob[ Γ ]} {a : D.Ob[ Γ ⨾ x ]} {b : D.Ob[ Γ ]}
      → (f : D.Hom[ id ] a (π*.F₀ x b))
      → ∐-transpose (∐-elim f) ≡ f
    ∐-transpose-elim {x = x} {a = a} {b = b} f = sym $
      D-fib.uniquep πᶜ b _ _ _ f $ symP $
      ⟨⟩-cocartesian.commutesp x a id-comm-sym (D-fib.lifting πᶜ b D.∘′ f)
```

<!--
```agda
  ∐-transpose-equiv
    : ∀ {Γ} {x : E.Ob[ Γ ]} {a : D.Ob[ Γ ⨾ x ]} {b : D.Ob[ Γ ]}
    → is-equiv (∐-transpose {a = a} {b = b})
  ∐-transpose-equiv = is-iso→is-equiv $
    iso ∐-elim ∐-transpose-elim ∐-elim-transpose
```
-->

`∐-transpose`{.Agda} is also natural.

```agda
  opaque
    unfolding ∐-transpose
    ∐-transpose-naturall
      : ∀ {Γ} {x : E.Ob[ Γ ]} {a b : D.Ob[ Γ ⨾ x ]} {c : D.Ob[ Γ ]}
      → (f : D.Hom[ id ] (∐ x b) c) (g : D.Hom[ id ] a b)
      → ∐-transpose f D.∘′ g D.≡[ idl _ ] ∐-transpose (f D↓.∘ ∐[ g ])
    ∐-transpose-naturall {x = x} {a = a} {b = b} {c = c} f g =
      D-fib.uniquep πᶜ c _ _ _ (∐-transpose f D.∘′ g) $
        D-fib.lifting πᶜ c D.∘′ ∐-transpose f D.∘′ g D.≡[]⟨ Dr.pulll[] id-comm (D-fib.commutesp πᶜ c _ _) ⟩
        (f D.∘′ ⟨ x , b ⟩) D.∘′ g                    D.≡[]⟨ Dr.extendr[] _ (symP (∐[]-natural g)) ⟩
        (f D.∘′ ∐[ g ]) D.∘′ ⟨ x , a ⟩               D.≡[ ap (_∘ πᶜ) (idl _) ]⟨ to-pathp (Dr.unwhisker-l (ap (_∘ πᶜ) (idl _)) (idl _)) ⟩
        (f D↓.∘ ∐[ g ]) D.∘′ ⟨ x , a ⟩               ∎

    ∐-transpose-naturalr
      : ∀ {Γ} {x : E.Ob[ Γ ]} {a : D.Ob[ Γ ⨾ x ]} {b c : D.Ob[ Γ ]}
      → (f : D.Hom[ id ] b c) (g : D.Hom[ id ] (∐ x a) b)
      → π*.₁ x f D.∘′ ∐-transpose g D.≡[ idl _ ] ∐-transpose (f D↓.∘ g)
    ∐-transpose-naturalr {x = x} {a = a} {b = b} {c = c} f g =
      D-fib.uniquep πᶜ c _ _ _ (π*.F₁ x f D.∘′ ∐-transpose g) $
        D-fib.lifting πᶜ c D.∘′ π*.₁ x f D.∘′ ∐-transpose g     D.≡[]⟨ Dr.pulll[] _ (D-fib.commutesp πᶜ c id-comm _) ⟩
        (f D.∘′ D-fib.lifting πᶜ b) D.∘′ ∐-transpose g          D.≡[]⟨ Dr.extendr[] id-comm (D-fib.commutesp πᶜ b _ _) ⟩
        (f D.∘′ g) D.∘′ ⟨ x , a ⟩                               D.≡[ ap (_∘ πᶜ) (idl _) ]⟨ to-pathp (Dr.unwhisker-l (ap (_∘ πᶜ) (idl _)) (idl _)) ⟩
        Dr.hom[ idl id ] (f D.∘′ g) D.∘′ ⟨ x , a ⟩              ∎
```

Next, we define an introduction form for coproducts that allows us
to apply a substitution.


```agda
  opaque
    ⟨_⨾_⟩
      : ∀ {Γ Δ x y} {σ : Hom Γ Δ}
      → (f : E.Hom[ σ ] x y) (a : D.Ob[ Δ ⨾ y ])
      → D.Hom[ πᶜ ] (D*.₀ (σ ⨾ˢ f) a) (D*.₀ σ (∐ y a))
    ⟨_⨾_⟩ {x = x} {y = y} {σ = σ} f a =
      D-fib.universal′ σ (∐ y a) (sym (sub-proj f)) $
      ⟨ y , a ⟩ D.∘′ D-fib.lifting (σ ⨾ˢ f) a

    ⟨⨾⟩-weaken
      : ∀ {Γ Δ x y} {σ : Hom Γ Δ}
      → (f : E.Hom[ σ ] x y) (a : D.Ob[ Δ ⨾ y ])
      → D-fib.lifting σ (∐ y a) D.∘′ ⟨ f ⨾ a ⟩
      D.≡[ sym (sub-proj f) ] ⟨ y , a ⟩ D.∘′ D-fib.lifting (σ ⨾ˢ f) a
    ⟨⨾⟩-weaken {y = y} {σ = σ} f a =
       D-fib.commutesp σ (∐ y a) (symP (sub-proj f)) _
```

Crucially, this map is also cocartesian due to stability of
cocartesian maps.

```agda
  opaque
    ⟨⨾⟩-cocartesian
      : ∀ {Γ Δ x y} {σ : Hom Γ Δ} → {f : E.Hom[ σ ] x y}
      → is-cartesian E σ f → (a : D.Ob[ Δ ⨾ y ])
      → is-cocartesian D πᶜ ⟨ f ⨾ a ⟩
    ⟨⨾⟩-cocartesian {x = x} {y = y} {σ = σ} {f = f} cart a =
      cocartesian-stable cart
        (symP (⟨⨾⟩-weaken f a))
        (⟨⟩-cocartesian y a)
        (D-fib.cartesian (σ ⨾ˢ f) a)
        (D-fib.cartesian σ (∐ y a))

  module ⟨⨾⟩-cocartesian
    {Γ Δ x y} {σ : Hom Γ Δ} {f : E.Hom[ σ ] x y}
    (cart : is-cartesian E σ f) (a : D.Ob[ Δ ⨾ y ])
    = is-cocartesian (⟨⨾⟩-cocartesian cart a)
```

```agda
  opaque
    unfolding ⟨_⨾_⟩
    ⟨⨾⟩-natural
      : ∀ {Γ Δ x y} {σ : Hom Γ Δ}
      → {a b : D.Ob[ Δ ⨾ y ]}
      → (f : D.Hom[ id ] a b) (g : E.Hom[ σ ] x y)
      → ⟨ g ⨾ b ⟩ D.∘′ D*.₁ (σ ⨾ˢ g) f D.≡[ id-comm ] D*.₁ σ ∐[ f ] D.∘′ ⟨ g ⨾ a ⟩
    ⟨⨾⟩-natural {x = x} {y = y} {σ = σ} {a = a} {b = b} f g =
      D-fib.uniquep₂ σ (∐ y b) _ _ _ _ _
        (Dr.pulll[] _ (D-fib.commutesp σ (∐ y b) (sym (sub-proj g)) _)
         D.∙[] Dr.pullr[] _ (D-fib.commutesp (σ ⨾ˢ g) b id-comm _))
        (Dr.pulll[] _ (D-fib.commutesp σ (∐ y b) id-comm _)
         D.∙[] Dr.pullr[] _ (⟨⨾⟩-weaken g a)
         D.∙[] Dr.extendl[] _ (∐[]-natural f))
```

This lets us extend a substitution $\Gamma, X \to \Delta, Y$ into
a substitution $\sigma^*(\coprod_{Y}A) \to \coprod_{(\sigma, f)^{*}(X)} A$.

```agda
  opaque
    ∐-sub
      : ∀ {Γ Δ x y} {σ : Hom Γ Δ} {f : E.Hom[ σ ] x y}
      → is-cartesian E σ f → (a : D.Ob[ Δ ⨾ y ])
      → D.Hom[ id ] (D*.₀ σ (∐ y a)) (∐ x (D*.₀ (σ ⨾ˢ f) a))
    ∐-sub {x = x} {σ = σ} {f = f} cart a =
      ⟨⨾⟩-cocartesian.universalv cart a ⟨ x , (D*.₀ (σ ⨾ˢ f) a) ⟩

    ∐-sub-⟨⨾⟩
      : ∀ {Γ Δ x y} {σ : Hom Γ Δ} {f : E.Hom[ σ ] x y}
      → (cart : is-cartesian E σ f) → (a : D.Ob[ Δ ⨾ y ])
      → ∐-sub cart a D.∘′ ⟨ f ⨾ a ⟩ D.≡[ idl _ ] ⟨ x , (D*.₀ (σ ⨾ˢ f) a) ⟩
    ∐-sub-⟨⨾⟩ cart a =
      ⟨⨾⟩-cocartesian.commutesv cart a _

    ∐-sub-natural
      : ∀ {Γ Δ x y} {σ : Hom Γ Δ} {f : E.Hom[ σ ] x y}
      → {a b : D.Ob[ Δ ⨾ y ]}
      → (cart : is-cartesian E σ f)
      → (g : D.Hom[ id ] a b)
      → ∐-sub cart b D.∘′ D*.₁ σ ∐[ g ] ≡ ∐[ D*.₁ (σ ⨾ˢ f) g ] D.∘′ ∐-sub cart a
    ∐-sub-natural {x = x} {y = y} {σ = σ} {f = f} {a = a} {b = b} cart g =
      ⟨⨾⟩-cocartesian.uniquep₂ cart a _ _ _ _ _
        (Dr.pullr[] _ (symP (⟨⨾⟩-natural g f))
         D.∙[] Dr.pulll[] _ (⟨⨾⟩-cocartesian.commutesv cart b _))
        (Dr.pullr[] _ (⟨⨾⟩-cocartesian.commutesv cart a _)
         D.∙[] ∐[]-natural (D*.₁ (σ ⨾ˢ f) g))
```
