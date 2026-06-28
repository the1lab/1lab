---
description: |
  Isofibrations.
---

<!--
```agda
open import Cat.Displayed.Cocartesian
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Morphism
import Cat.Morphism
```
-->

```agda
module Cat.Displayed.Isofibration where
```

<!--
```agda
private
  variable
    ob ℓb oe ℓe : Level
    B : Precategory ob ℓb

  level : {B : Precategory ob ℓb} → Displayed B oe ℓe → Level
  level {ob = ob} {ℓb = ℓb} {oe = oe} {ℓe = ℓe} _ = ob ⊔ ℓb ⊔ oe ⊔ ℓe
```
-->

# Isofibrations {defines=isofibration}

```agda
record Isofibration (E : Displayed B oe ℓe) : Type (level E) where
```

<!--
```agda
  no-eta-equality

  open Cat.Displayed.Morphism E
  open Cat.Morphism B
  open Displayed E
```
-->

An **isofibration** $\cE \liesover \cB$ is a [[displayed category]]
admitting a notion of *transport* between [[fibres|fibre category]] over
isomorphic objects. Explicitly, this means that every lifting diagram of
the form below can be extended to one with the dotted arrows, where both
$u$ is an isomorphism and $u'$ an isomorphism *over* $u$.

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  {a'} \&\& {b'} \\
  \\
  a \&\& b
  \arrow["{u'}", dashed, from=1-1, to=1-3]
  \arrow[dashed, maps to, from=1-1, to=3-1]
  \arrow[maps to, from=1-3, to=3-3]
  \arrow["u"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

```agda
  field
    _^*_     : ∀ {a b} (u : a ≅ b) (a' : Ob[ a ]) → Ob[ b ]
    ^*-lifts : ∀ {a b} (u : a ≅ b) (a' : Ob[ a ]) → a' ≅[ u ] (u ^* a')
```

<!--
```agda
  private
    open module ^*-lifts {a b} {f : a ≅ b} {x : Ob[ a ]} = _≅[_]_ (^*-lifts f x)
      public using ()
      renaming (to' to π* ; from' to ι!)
```
-->

We write the components of the displayed isomorphism `^*-lifts`{.Agda}
as `π*`{.Agda} and `ι!`{.Agda}: these are, respectively, maps $u^*b' \to
b'$ and $b' \to u^*b'$. Since they are invertible, they provide
[[cartesian|cartesian morphism]] (respectively [[cocartesian|cocartesian
morphism]]) lifts of $b'$ along $u$.

```agda
  π*-is-cartesian   : ∀ {a b} (u : a ≅ b) b' → is-cartesian   E (u .to)   π*
  ι!-is-cocartesian : ∀ {a b} (u : a ≅ b) b' → is-cocartesian E (u .from) ι!

  π*-is-cartesian u x = invertible→cartesian E _ $
    iso[]→invertible[] (^*-lifts u x)

  ι!-is-cocartesian u x = invertible→cocartesian E _ $
    iso[]→invertible[] (^*-lifts u x Iso[]⁻¹)
```

## Over categories

<!--
```agda
{-# INLINE Isofibration.constructor #-}

module _ {B : Precategory ob ℓb} (E : Displayed B oe ℓe) (bcat : is-category B) where
  open Cat.Displayed.Morphism E
  open Displayed E

  open Univalent bcat
  open Isofibration
```
-->

If $\cB$ is [[univalent|univalent category]], then every category $\cE
\liesover \cB$ displayed over it is an isofibration. This follows by a
simple argument using *isomorphism* induction. We first rearrange the
data of `Isofibration`{.Agda} into a family of products that manifestly
depends on the objects $a, b : \cB$ and the isomorphism $a \cong b$. It
is easy to rearrange a section of this family into an instance of
`Isofibration`{.Agda}.

```agda
  private
    Lifts : ∀ {a} b (u : a ≅ b) → Type _
    Lifts {a} b u = (a' : E ʻ a) → Σ[ b' ∈ E ʻ b ] (a' ≅[ u ] b')

    from-lifts : (∀ {a b} u → Lifts {a} b u) → Isofibration E
    from-lifts l ._^*_     u b' = l u b' .fst
    from-lifts l .^*-lifts u b' = l u b' .snd
```

The reason for this rephrasing is that `Lifts`{.Agda} is precisely a
*motive* for isomorphism induction. Accordingly, to obtain a section of
this family, it suffices to give isomorphic lifts along the identity;
for which we may take the identity isomorphism, completing the proof.

```agda
  is-category→isofibration : Isofibration E
  is-category→isofibration = from-lifts $ J-iso Lifts λ b' →
    b' , id-iso↓
```
