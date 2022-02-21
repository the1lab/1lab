```agda
open import Cat.Prelude

module Cat.Diagram.Duals {o h} (C : Precategory o h) where
```

<!--
```agda
import Cat.Reasoning C as C
```
-->

# Dualities of diagrams

Following [Hu and Carette][agda-categories], we've opted to have
_different_ concrete definitions for diagrams and their opposites. In
particular, we have the following pairs of "redundant" definitions:

[agda-categories]: https://arxiv.org/abs/2005.07059

- Products and coproducts
- Pullbacks and pushouts
- Equalisers and coequalisers
- Terminal objects and initial objects

For all four of the above pairs, we have that one in $C$ is the other in
$C\op$. We prove these correspondences here:

## Co/products

```agda
import Cat.Diagram.Product (C ^op) as Co-prod
import Cat.Diagram.Coproduct C as Coprod

is-co-product→is-coproduct 
  : ∀ {A B P} {i1 : C.Hom A P} {i2 : C.Hom B P} 
  → Co-prod.is-product i1 i2 → Coprod.is-coproduct i1 i2
is-co-product→is-coproduct isp = 
  record 
    { [_,_]      = isp.⟨_,_⟩
    ; in₀∘factor = isp.π₁∘factor
    ; in₁∘factor = isp.π₂∘factor
    ; unique     = isp.unique
    }
  where module isp = Co-prod.is-product isp

is-coproduct→is-co-product 
  : ∀ {A B P} {i1 : C.Hom A P} {i2 : C.Hom B P} 
  → Coprod.is-coproduct i1 i2 → Co-prod.is-product i1 i2
is-coproduct→is-co-product iscop = 
  record 
    { ⟨_,_⟩     = iscop.[_,_] 
    ; π₁∘factor = iscop.in₀∘factor 
    ; π₂∘factor = iscop.in₁∘factor
    ; unique    = iscop.unique
    }
  where module iscop = Coprod.is-coproduct iscop
```

## Co/equalisers

```agda
import Cat.Diagram.Equaliser (C ^op) as Co-equ
import Cat.Diagram.Coequaliser C as Coequ

is-co-equaliser→is-coequaliser
  : ∀ {A B E} {f g : C.Hom A B} {coeq : C.Hom B E} 
  → Co-equ.is-equaliser f g coeq → Coequ.is-coequaliser f g coeq
is-co-equaliser→is-coequaliser eq = 
  record
    { coequal    = eq.equal 
    ; coequalise = eq.limiting 
    ; universal  = eq.universal 
    ; unique     = eq.unique 
    }
  where module eq = Co-equ.is-equaliser eq

is-coequaliser→is-co-equaliser
  : ∀ {A B E} {f g : C.Hom A B} {coeq : C.Hom B E} 
  → Coequ.is-coequaliser f g coeq → Co-equ.is-equaliser f g coeq
is-coequaliser→is-co-equaliser coeq = 
  record 
    { equal     = coeq.coequal 
    ; limiting  = coeq.coequalise 
    ; universal = coeq.universal 
    ; unique    = coeq.unique 
    }
  where module coeq = Coequ.is-coequaliser coeq
```

## Initial/terminal

```agda
import Cat.Diagram.Terminal (C ^op) as Coterm
import Cat.Diagram.Initial C as Init

is-initial→is-coterminal
  : ∀ {A} → Coterm.is-terminal A → Init.is-initial A
is-initial→is-coterminal x = x

is-coterminal→is-initial
  : ∀ {A} → Init.is-initial A → Coterm.is-terminal A
is-coterminal→is-initial x = x
```

## Pullback/pushout

```agda
import Cat.Diagram.Pullback (C ^op) as Co-pull
import Cat.Diagram.Pushout C as Push

is-co-pullback→is-pushout
  : ∀ {P X Y Z} {p1 : C.Hom X P} {f : C.Hom Z X} {p2 : C.Hom Y P} {g : C.Hom Z Y}
  → Co-pull.is-pullback p1 f p2 g → Push.is-pushout f p1 g p2
is-co-pullback→is-pushout pb = 
  record
    { square = pb.square 
    ; colimiting = pb.limiting
    ; i₁∘colimiting = pb.p₁∘limiting
    ; i₂∘colimiting = pb.p₂∘limiting
    ; unique = pb.unique
    }
  where module pb = Co-pull.is-pullback pb

is-pushout→is-co-pullback
  : ∀ {P X Y Z} {p1 : C.Hom X P} {f : C.Hom Z X} {p2 : C.Hom Y P} {g : C.Hom Z Y}
  → Push.is-pushout f p1 g p2 → Co-pull.is-pullback p1 f p2 g
is-pushout→is-co-pullback po = 
  record
    { square      = po.square
    ; limiting    = po.colimiting
    ; p₁∘limiting = po.i₁∘colimiting
    ; p₂∘limiting = po.i₂∘colimiting
    ; unique      = po.unique
    }
  where module po = Push.is-pushout po
```

<!-- TODO [Amy 2022-02-21]
co/cones
co/limits
-->