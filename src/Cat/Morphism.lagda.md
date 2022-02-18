```agda
open import 1Lab.Prelude hiding (_∘_ ; id ; _↪_)

open import Cat.Solver
open import Cat.Base

module Cat.Morphism {o h} (C : Precategory o h) where
```

<!--
```agda
open Precategory C public
private variable
  a b c d : Ob
```
-->

# Morphisms

This module defines the three most important classes of morphisms that
can be found in a category: **monomorphisms**, **epimorphisms**, and
**isomorphisms**.

## Monos

A morphism is said to be **monic** when it is left-cancellable. A
**monomorphism** from $A$ to $B$, written $A \mono B$, is a monic
morphism.

```agda
isMonic : Hom a b → Type _
isMonic {a = a} f = ∀ {c} → (g h : Hom c a) → f ∘ g ≡ f ∘ h → g ≡ h

record _↪_ (a b : Ob) : Type (o ⊔ h) where
  field
    mor   : Hom a b
    monic : isMonic mor
```

Conversely, a morphism is said to be **epic** when it is
right-cancellable.  An **epimorphism** from $A$ to $B$, written $A \epi
B$, is an epic morphism.

## Epis

```agda
isEpic : Hom a b → Type _
isEpic {b = b} f = ∀ {c} → (g h : Hom b c) → g ∘ f ≡ h ∘ f → g ≡ h

record _↠_ (a b : Ob) : Type (o ⊔ h) where
  field
    mor   : Hom a b
    monic : isEpic mor
```

## Isos

Maps $f : A \to B$ and $g : B \to A$ are **inverses** when we have $f
\circ g$ and $g \circ f$ both equal to the identity. A map $f : A \to B$
**is invertible** (or **is an isomorphism**) when there exists a $g$ for
which $f$ and $g$ are inverses. An **isomorphism** $A \cong B$ is a
choice of map $A \to B$, together with a specified inverse.

```agda
record Inverses (f : Hom a b) (g : Hom b a) : Type h where
  field
    invˡ : f ∘ g ≡ id
    invʳ : g ∘ f ≡ id
  
open Inverses

record isInvertible (f : Hom a b) : Type (o ⊔ h) where
  field
    inv : Hom b a
    inverses : Inverses f inv
  
  open Inverses inverses public

  op : isInvertible inv
  op .inv = f
  op .inverses .Inverses.invˡ = invʳ inverses
  op .inverses .Inverses.invʳ = invˡ inverses

record _≅_ (a b : Ob) : Type (o ⊔ h) where
  field
    to       : Hom a b
    from     : Hom b a
    inverses : Inverses to from
  
  open Inverses inverses public

open _≅_ public
```

A given map is invertible in at most one way: If you have $f : A \to B$
with two _inverses_ $g : B \to A$ and $h : B \to A$, then not only are
$g = h$ equal, but the witnesses of these equalities are irrelevant.

```agda
isProp-Inverses : ∀ {f : Hom a b} {g : Hom b a} → isProp (Inverses f g)
isProp-Inverses x y i .Inverses.invˡ = Hom-set _ _ _ _ (x .invˡ) (y .invˡ) i
isProp-Inverses x y i .Inverses.invʳ = Hom-set _ _ _ _ (x .invʳ) (y .invʳ) i

isProp-isInvertible : ∀ {f : Hom a b} → isProp (isInvertible f)
isProp-isInvertible {a = a} {b = b} {f = f} g h = p where
  module g = isInvertible g
  module h = isInvertible h

  g≡h : g.inv ≡ h.inv
  g≡h = 
    g.inv             ≡⟨ sym (idr _) ∙ ap₂ _∘_ refl (sym h.invˡ) ⟩
    g.inv ∘ f ∘ h.inv ≡⟨ assoc _ _ _ ·· ap₂ _∘_ g.invʳ refl ·· idl _ ⟩ 
    h.inv             ∎
  
  p : g ≡ h
  p i .isInvertible.inv = g≡h i
  p i .isInvertible.inverses =
    isProp→PathP (λ i → isProp-Inverses {g = g≡h i}) g.inverses h.inverses i
```

We note that the identity morphism is always iso, and that isos compose:

<!--
```agda
makeIso : (f : Hom a b) (g : Hom b a) → f ∘ g ≡ id → g ∘ f ≡ id → a ≅ b
makeIso f g p q ._≅_.to = f
makeIso f g p q ._≅_.from = g
makeIso f g p q ._≅_.inverses .Inverses.invˡ = p
makeIso f g p q ._≅_.inverses .Inverses.invʳ = q

isSet-≅ : isSet (a ≅ b)
isSet-≅ x y p q = s where
  open _≅_
  open Inverses

  s : p ≡ q
  s i j .to = Hom-set _ _ (x .to) (y .to) (ap to p) (ap to q) i j
  s i j .from = Hom-set _ _ (x .from) (y .from) (ap from p) (ap from q) i j
  s i j .inverses =
    isProp→SquareP
      (λ i j → isProp-Inverses {f = Hom-set _ _ (x .to) (y .to) (ap to p) (ap to q) i j}
                               {g = Hom-set _ _ (x .from) (y .from) (ap from p) (ap from q) i j})
      (λ i → x .inverses) (λ i → p i .inverses) (λ i → q i .inverses) (λ i → y .inverses) i j

≅-PathP : (p : a ≡ c) (q : b ≡ d)
        → {f : a ≅ b} {g : c ≅ d}
        → PathP (λ i → Hom (p i) (q i)) (f ._≅_.to) (g ._≅_.to)
        → PathP (λ i → Hom (q i) (p i)) (f ._≅_.from) (g ._≅_.from)
        → PathP (λ i → p i ≅ q i) f g
≅-PathP p q r s i .to = r i
≅-PathP p q r s i .from = s i
≅-PathP p q {f} {g} r s i .inverses = 
  isProp→PathP (λ j → isProp-Inverses {f = r j} {g = s j}) 
    (f .inverses) (g .inverses) i
```
-->

```agda
idIso : a ≅ a
idIso = makeIso id id (idl _) (idl _)

Inverses-∘ : {f : Hom a b} {f⁻¹ : Hom b a} {g : Hom b c} {g⁻¹ : Hom c b}
           → Inverses f f⁻¹ → Inverses g g⁻¹ → Inverses (g ∘ f) (f⁻¹ ∘ g⁻¹)
Inverses-∘ {f = f} {f⁻¹} {g} {g⁻¹} finv ginv = record { invˡ = l ; invʳ = r } where
  module finv = Inverses finv
  module ginv = Inverses ginv

  abstract
    l : (g ∘ f) ∘ f⁻¹ ∘ g⁻¹ ≡ id
    l = (g ∘ f) ∘ f⁻¹ ∘ g⁻¹ ≡⟨ solve C ⟩
        g ∘ (f ∘ f⁻¹) ∘ g⁻¹ ≡⟨ (λ i → g ∘ finv.invˡ i ∘ g⁻¹) ⟩
        g ∘ id ∘ g⁻¹        ≡⟨ solve C ⟩
        g ∘ g⁻¹             ≡⟨ ginv.invˡ ⟩
        id                  ∎
    
    r : (f⁻¹ ∘ g⁻¹) ∘ g ∘ f ≡ id
    r = (f⁻¹ ∘ g⁻¹) ∘ g ∘ f ≡⟨ solve C ⟩
        f⁻¹ ∘ (g⁻¹ ∘ g) ∘ f ≡⟨ (λ i → f⁻¹ ∘ ginv.invʳ i ∘ f) ⟩
        f⁻¹ ∘ id ∘ f        ≡⟨ solve C ⟩
        f⁻¹ ∘ f             ≡⟨ finv.invʳ ⟩
        id                  ∎

_∘Iso_ : a ≅ b → b ≅ c → a ≅ c
(f ∘Iso g) .to = g .to ∘ f .to
(f ∘Iso g) .from = f .from ∘ g .from
(f ∘Iso g) .inverses = Inverses-∘ (f .inverses) (g .inverses)

_Iso⁻¹ : a ≅ b → b ≅ a
(f Iso⁻¹) .to = f .from
(f Iso⁻¹) .from = f .to
(f Iso⁻¹) .inverses .invˡ = f .inverses .invʳ
(f Iso⁻¹) .inverses .invʳ = f .inverses .invˡ
```
