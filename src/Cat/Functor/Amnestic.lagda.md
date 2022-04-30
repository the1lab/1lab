```agda
open import Cat.Functor.Base
open import Cat.Prelude
open import Cat.Univalent

import Cat.Functor.Reasoning as Func
import Cat.Reasoning as Cat

module Cat.Functor.Amnestic where
```

<!--
```agda
private variable
  o ℓ o′ ℓ′ : Level
  C D : Precategory o ℓ
```
-->

# Amnestic functors

The notion of **amnestic functor** was introduced by Adámek, Herrlich
and Strecker in their book "The Joy of Cats"^[Cats are, indeed, very
joyful] as a way to make precise the vibes-based notion of **forgetful
functor**. Classically, the definition reads

> A functor $F : \ca{C} \to \ca{D}$ is **amnestic** if an isomorphism
$f$ _is an identity_ whenever $Ff$ is,

but what does it mean for an isomorphism $f : a \cong b$ to _be an
identity_? The obvious translation would be that $f$ comes from an
identification $a \equiv b$ of objects, but this is just rephrasing the
condition that $\ca{C}$ is univalent, whereas we want a condition on the
_functor_ $F$. So, we define:

An isomorphism $f : a \cong b$ **is an identity** if it is an identity
in the total space of `Hom`{.Agda}, i.e. if there is an object $c :
\ca{C}$ s.t. $(c, c, \id{id}) = (a, b, f)$ in the type $\Sigma_a
\Sigma_b (a \to b)$. Every isomorphism in a univalent category is an
identity, since we can take $c = a$, and the identification in
`Mor`{.Agda} follows from univalence.

```agda
Mor : Precategory o ℓ → Type (o ⊔ ℓ)
Mor C = Σ[ a ∈ Cat.Ob C ] Σ[ b ∈ Cat.Ob C ] Cat.Hom C a b
```

<!--
```agda
Hom→Mor : (C : Precategory o ℓ) {x y : Cat.Ob C} → Cat.Hom C x y → Mor C
Hom→Mor _ f = _ , _ , f

Mor-path : (C : Precategory o ℓ) {a b : Mor C}
         → (p : a .fst ≡ b .fst)
         → (q : a .snd .fst ≡ b .snd .fst)
         → PathP (λ i → Cat.Hom C (p i) (q i)) (a .snd .snd) (b .snd .snd)
         → a ≡ b
Mor-path C p q r i = p i , q i , r i

module _ (F : Functor C D) where
  private
    module C = Cat C
    module D = Cat D
    module F = Func F
```
-->

Let $f$ be an identity, i.e. it is such that $(a, b, f) \cong (c, c,
\id{id})$. Any functor $F$ induces an identification $(Fa, Fb, Ff) \cong
(Fc, Fc, id)$, meaning that it _preserves being an identity_. A functor
is **amnestic** if it additionally _reflects_ being an identity: the
natural map we have implicitly defined above (called `action`{.Agda}) is
an equivalence.

```agda
  action : ∀ {a b : C.Ob} (f : C.Hom a b)
          → Σ[ c ∈ C.Ob ] (Hom→Mor C (C.id {x = c}) ≡ Hom→Mor C f)
          → Σ[ c ∈ D.Ob ] (Hom→Mor D (D.id {x = c}) ≡ Hom→Mor D (F.₁ f))
  action f (c , p) = F.₀ c , q where
    q : Hom→Mor D D.id ≡ Hom→Mor D (F.₁ f)
    q i .fst = F.₀ (p i .fst)
    q i .snd .fst = F.₀ (p i .snd .fst)
    q i .snd .snd =
      hcomp
        (λ { j (i = i0) → F.F-id j
           ; j (i = i1) → F.F₁ f
           })
        (F.₁ (p i .snd .snd))

  is-amnestic : Type _
  is-amnestic = ∀ {a b : C.Ob} (f : C.Hom a b)
              → C.is-invertible f → is-equiv (action f)
```

# Who cares?

The amnestic functors are interesting to consider in HoTT because they
are exactly those that _reflect univalence_: If $F : \ca{C} \to \ca{D}$
is an amnestic functor and $\ca{D}$ is a univalent category, then
$\ca{C}$ is univalent, too!

```agda
  reflect-category : is-category D → is-amnestic → is-category C
  reflect-category d-cat forget A = contr (_ , C.id-iso) uniq where
    uniq : ∀ x → (A , C.id-iso) ≡ x
    uniq (B , isom) = Σ-pathp A≡B q where
      isom′ = F-map-iso F isom
```

For suppose that $i : a \cong b \in \ca{C}$ is an isomorphism. $F$
preserves this isomorphism, meaning we have an iso $Fi : Fa \cong Fb$,
now in $\ca{D}$. But because $\ca{D}$ is a univalent category, $Fi$ is
an identity, and by $F$'s amnesia, so is $i$.

```agda
      p : Σ[ c ∈ C.Ob ] Path (Mor C) (c , c , C.id) (A , B , isom .C.to)
      p = equiv→inverse (forget (isom .C.to) (C.iso→invertible isom)) $
            F.₀ A , Mor-path D refl (iso→path D d-cat isom′)
                      (Hom-pathp-reflr-iso D d-cat (D.idr _))
```

Unfolding, we have an object $x : \ca{C}$ and an identification $p : (x,
x, \id{id}) \equiv (a, b, i)$. We may construct an identification $p' :
a \cong b$ from the components of $p$, and this induces an
identification $\id{id} \equiv i$ over $p'$ in a straightforward way.
We're done!

```agda
      A≡B = sym (ap fst (p .snd)) ∙ ap (fst ⊙ snd) (p .snd)

      q : PathP (λ i → A C.≅ A≡B i) C.id-iso isom
      q = C.≅-pathp refl A≡B $ Hom-pathp-reflr C $
           C.idr _
        ·· path→to-∙ C _ _
        ·· ap₂ C._∘_ refl (sym (path→to-sym C (ap fst (p .snd))))
         ∙ Hom-pathp-id C (ap (snd ⊙ snd) (p .snd))
```
