<!--
```agda
open import Cat.Functor.Hom.Representable
open import Cat.Functor.Naturality
open import Cat.Functor.Kan.Base
open import Cat.Functor.Compose
open import Cat.Functor.Base
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Functor.Kan.Representable where
```

## Representability of Kan extensions

Like most constructions with a universal property, we can phrase the
definition of [[Kan extensions]] in terms of an equivalence of $\hom$
functors. This rephrasing lets us construct extensions in terms of
chains of natural isomorphisms, which can be very handy!

<!--
```agda
module _
  {o ℓ o' ℓ'}
  {C : Precategory o ℓ} {C' : Precategory o ℓ} {D : Precategory o' ℓ'}
  {p : Functor C C'} {F : Functor C D} {G : Functor C' D}
  where
  private
    module C = Cat.Reasoning C
    module C' = Cat.Reasoning C'
    module D = Cat.Reasoning D
    module [C',D] = Cat.Reasoning Cat[ C' , D ]
    module [C,D] = Cat.Reasoning Cat[ C , D ]
    open Functor
    open _=>_
    open is-lan
    open Corepresentation
    open Isoⁿ
```
-->

Let $p : \cC \to \cC'$, and $F : \cC \to \cD$, and $(G, \eta)$ be
a candidate for a left extension, as in the following diagram.

~~~{.quiver}
\begin{tikzcd}
  && {\cC'} \\
  \\
  \cC &&&& \cD
  \arrow[""{name=0, anchor=center, inner sep=0}, "F"', from=3-1, to=3-5]
  \arrow["p"', from=3-1, to=1-3]
  \arrow["G"', from=1-3, to=3-5]
  \arrow["\eta"', shorten <=4pt, shorten >=7pt, Rightarrow, from=1-3, to=0]
\end{tikzcd}
~~~

Any such pair $(G, \eta)$ induces a natural transformation
$D^{C'}(G, -) \to D^{C}(F, - \circ p)$.

```agda
  Hom-from-precompose
    : F => G F∘ p
    → Hom-from Cat[ C' , D ] G => Hom-from Cat[ C , D ] F F∘ precompose p
  Hom-from-precompose eta .η H α = (α ◂ p) ∘nt eta
  Hom-from-precompose eta .is-natural H K α = funext λ β → [C,D].pushl ◂-distribl
```

If this natural transformation is an isomorphism, then $(G, \eta)$ is a
left Kan extension of $F$ along $p$.

```agda
  represents→is-lan
    : (eta : F => G F∘ p)
    → is-invertibleⁿ (Hom-from-precompose eta)
    → is-lan p F G eta
  represents→is-lan eta nat-inv = lan where
```

This may seem somewhat difficult to prove at first glance, but it ends
up being an exercise in shuffling data around. We can use the inverse
to `Hom-from-precompose eta` to obtain the universal map of the extension, and
factorisation/uniqueness follow directly from the fact that we have
a natural isomorphism.

```agda
    module nat-inv = is-invertibleⁿ nat-inv

    lan : is-lan p F G eta
    lan .σ {M} α = nat-inv.inv .η M α
    lan .σ-comm {M} {α} = nat-inv.invl ηₚ M $ₚ α
    lan .σ-uniq {M} {α} {σ'} q = ap (nat-inv.inv .η M) q ∙ nat-inv.invr ηₚ M $ₚ σ'
```

Furthermore, if $(G, \eta)$ is a left extension, then we can show that
`Hom-from-precompose eta` is a natural isomorphism. The proof is yet another
exercise in moving data around.

```agda
  is-lan→represents
    : {eta : F => G F∘ p}
    → is-lan p F G eta
    → is-invertibleⁿ (Hom-from-precompose eta)
  is-lan→represents {eta} lan =
    to-is-invertibleⁿ inv
      (λ M → funext λ α → lan .σ-comm)
      (λ M → funext λ α → lan .σ-uniq refl)
    where
      inv : Hom-from Cat[ C , D ] F F∘ precompose p => Hom-from Cat[ C' , D ] G
      inv .η M α = lan .σ α
      inv .is-natural M N α = funext λ β →
        lan .σ-uniq (ext λ _ → D.pushr (sym $ lan .σ-comm ηₚ _))
```

<!--
```agda
module _
  {o ℓ o' ℓ'}
  {C : Precategory o ℓ} {C' : Precategory o ℓ} {D : Precategory o' ℓ'}
  {p : Functor C C'} {F : Functor C D} {L : Functor C' D} {ψ : F => L F∘ p}
  where
  private
    module C = Cat.Reasoning C
    module C' = Cat.Reasoning C'
    module D = Cat.Reasoning D
    module [C',D] = Cat.Reasoning Cat[ C' , D ]
    module [C,D] = Cat.Reasoning Cat[ C , D ]
    open Functor
    open _=>_
    open Isoⁿ
```
-->

```agda
  is-lan→is-corepresentation
    : is-lan p F L ψ
    → is-corepresentation (Hom-from Cat[ C , D ] F F∘ precompose p) L ψ
  {-# INLINE is-lan→is-corepresentation #-}
  is-lan→is-corepresentation lan = record
    { universal = lan.σ
    ; factors = λ α → lan.σ-comm
    ; unique = λ α ξ p → lan.σ-uniq (sym p)
    }
    where module lan = is-lan lan

  is-corepresentation→is-lan
    : is-corepresentation (Hom-from Cat[ C , D ] F F∘ precompose p) L ψ
    → is-lan p F L ψ
  is-corepresentation→is-lan corep = record
    { σ = corep.universal
    ; σ-comm = λ {M} {α} → corep.factors α
    ; σ-uniq = λ {M} {α} {σ'} p → corep.unique α σ' (sym p)
    }
    where module corep = is-corepresentation corep
```
