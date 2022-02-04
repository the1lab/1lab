```agda
open import 1Lab.Prelude

open import Algebra.Group

open import Data.Power

module Algebra.Group.Subgroup where
```

<!--
```agda
private variable
  ℓ ℓ' : Level
  G : Group ℓ
```
-->

# Subgroups

A **subgroup** $H$ of a group $(G, \star)$ is a subset of $G$ which
contains the group zero, and is closed under taking inverses and the
group multiplication.

```agda
record isSubgroup (G : Group ℓ) (H : ℙ (G .fst)) : Type ℓ where
  open GroupOn (G .snd)

  field
    has-unit : unit ∈ H
    has-⋆    : ∀ {x y} → x ∈ H → y ∈ H → (x ⋆ y) ∈ H
    has-inv  : ∀ {x} → x ∈ H → x ⁻¹ ∈ H
```

As the name implies, the subgroups of $(G, \star)$ are precisely those
subsets of $G$ which form a group under (the restriction of) $\star$.

```agda
isSubgroup→GroupOn 
  : (H : ℙ (G .fst)) → isSubgroup G H → GroupOn (Σ[ x ∈ G .fst ] x ∈ H)
isSubgroup→GroupOn {G = G} H sg = 
  makeGroup
    (isHLevelΣ 2 hasIsSet λ x → isProp→isSet (H x .snd))
    (unit , has-unit)
    (λ { (x , xin) (y , yin) → x ⋆ y , has-⋆ xin yin} )
    (λ { (x , xin) → (x ⁻¹ , has-inv xin) })
    (λ x y z → Σ≡Prop (λ x → H x .snd) (sym associative))
    (λ x → Σ≡Prop (λ x → H x .snd) inverseˡ)
    (λ x → Σ≡Prop (λ x → H x .snd) inverseʳ)
    (λ x → Σ≡Prop (λ x → H x .snd) idˡ)
  where open GroupOn (G .snd)
        open isSubgroup sg
```

## Normal Subgroups

We say that a subset $N$ is a **normal subgroup** of $G$ if it is, in
addition to a subgroup, closed under conjugation by elements of $G$.

```agda
record isNormal (G : Group ℓ) (N : ℙ (G .fst)) : Type ℓ where
  open GroupOn (G .snd)

  field
    has-subgroup : isSubgroup G N
    has-conjugate : ∀ {x y} → y ∈ N → (x ⋆ y ⋆ x ⁻¹) ∈ N

  has-conjugateˡ : ∀ {x y} → y ∈ N → ((x ⋆ y) ⋆ x ⁻¹) ∈ N
  has-conjugateˡ yin = subst (_∈ N) associative (has-conjugate yin)

  has-comm : ∀ {x y} → (x ⋆ y) ∈ N → (y ⋆ x) ∈ N
  has-comm {x = x} {y} ∈ = subst (_∈ N) p (has-conjugate ∈)
    where
      p = x ⁻¹ ⋆ (x ⋆ y) ⋆ x ⁻¹ ⁻¹ ≡⟨ ap₂ _⋆_ refl (sym associative) ∙ (λ i → x ⁻¹ ⋆ x ⋆ y ⋆ inv-inv {x = x} i) ⟩ 
          x ⁻¹ ⋆ x ⋆ y ⋆ x         ≡⟨ associative ⟩
          (x ⁻¹ ⋆ x) ⋆ y ⋆ x       ≡⟨ ap₂ _⋆_ inverseˡ refl ∙ idˡ ⟩
          y ⋆ x                    ∎
  
  open isSubgroup has-subgroup public
```

We note in passing that if a group $G$ is commutative, then every
subgroup $H$ of $G$ is normal. This is because in a commutative group,
conjugation by any element is always the identity: $xyx^{-1} = yxx^{-1}
= y$.

```agda
isAbelian→isNormal 
  : {H : ℙ (G .fst)} → isAbelian G → isSubgroup G H → isNormal G H
isAbelian→isNormal {G = G} {H = H} abelian sg = r where
  open GroupOn (G .snd)
  open isNormal

  commute-conjugate : ∀ x y → (x ⋆ y ⋆ x ⁻¹) ≡ y
  commute-conjugate x y =
    x ⋆ y ⋆ x ⁻¹   ≡⟨ ap₂ _⋆_ refl (abelian _ _) ⟩
    x ⋆ x ⁻¹ ⋆ y   ≡⟨ associative ⟩
    (x ⋆ x ⁻¹) ⋆ y ≡⟨ ap₂ _⋆_ inverseʳ refl ∙ idˡ ⟩
    y              ∎

  r : isNormal _ _
  r .has-subgroup = sg
  r .has-conjugate x = subst (_∈ H) (sym (commute-conjugate _ _)) x
```

We have a convenient packaging of normal subgroups as a record:

```agda
record NormalSubgroup (G : Group ℓ) : Type (lsuc ℓ) where
  field
    subgroup    : ℙ (G .fst)
    hasIsNormal : isNormal G subgroup

  open isNormal hasIsNormal public
```

# Kernels and Images

We can canonically associate to any group homomorphism $f : A \to B$ two
subgroups, one of $B$ and one of $A$: The **kernel** $\mathrm{ker}(f)$
is the (normal) subgroup of $A$ which $f$ maps to the identity of $B$,
and the **image** $\mathrm{im}(f)$ is the subgroup of $B$ which $f$ can
"reach". We start with the kernel:

```agda
module _ {A B : Group ℓ} (f : A .fst → B .fst) (h : isGroupHom A B f) where
  private
    module A = GroupOn (A .snd)
    module B = GroupOn (B .snd)
    module h = isGroupHom h

  open isSubgroup

  inKernel : ℙ (A .fst)
  inKernel x = (f x ≡ B.unit) , B.hasIsSet _ _
```

That the kernel is a subgroup follows from the properties of a group
homomorphism: They preserve multiplication, the group identity, and
inverses.

```agda
  ker-subgroup : isSubgroup A inKernel
  ker-subgroup .has-unit = h.pres-id
  ker-subgroup .has-⋆ {x = x} {y = y} fx=1 fy=1 = 
    f (x A.⋆ y)       ≡⟨ h.pres-⋆ x y ⟩
    f x B.⋆ f y       ≡⟨ ap₂ B._⋆_ fx=1 fy=1 ⟩
    B.unit B.⋆ B.unit ≡⟨ B.idˡ ⟩ 
    B.unit            ∎
  ker-subgroup .has-inv fx=1 = h.pres-inv _ ·· ap B.inverse fx=1 ·· B.inv-unit≡unit

  open isNormal
```

Normality follows from a slightly annoying calculation: We must show
that $f(xyx^{-1}) = 1$ (given $f(y) = 1$), which follows because we can
turn that into $f(x)f(y)f(x)^{-1}$, remove the $f(y)$ from the middle,
and cancel the remaining $f(x)f(x)^{-1}$.

```agda
  ker-normal : isNormal A inKernel
  ker-normal .has-subgroup = ker-subgroup
  ker-normal .has-conjugate {x = x} {y = y} fy=1 = 
    f (x A.⋆ y A.⋆ x A.⁻¹)        ≡⟨ h.pres-⋆ _ _ ⟩
    f x B.⋆ f (y A.⋆ x A.⁻¹)      ≡⟨ ap₂ B._⋆_ refl (h.pres-⋆ _ _) ⟩
    f x B.⋆ (f y B.⋆ f (x A.⁻¹))  ≡⟨ ap₂ B._⋆_ refl (ap₂ B._⋆_ fy=1 refl ∙ B.idˡ) ⟩
    f x B.⋆ f (x A.⁻¹)            ≡⟨ ap₂ B._⋆_ refl (h.pres-inv x) ⟩
    f x B.⋆ (f x) B.⁻¹            ≡⟨ B.inverseʳ ⟩
    B.unit                        ∎

  ker : NormalSubgroup A
  ker = record { subgroup = inKernel ; hasIsNormal = ker-normal }

  kerᴳ : Group ℓ
  kerᴳ = _ , isSubgroup→GroupOn _ ker-subgroup
```

Now we turn to the image, $\mathrm{im}(f)$. An element $y : B$ is in the
image if _there exists_ an $x : A$ such that $f(x)=y$.

```agda
  inImage : ℙ (B .fst)
  inImage y = (∃[ x ∈ A .fst ] (f x ≡ y)) , squash

  image-subgroup : isSubgroup B inImage
  image-subgroup .has-unit = inc (A.unit , h.pres-id)
  image-subgroup .has-⋆ {x} {y} = ∥-∥-map₂ λ where
    (f*x , p) (f*y , q) → (f*x A.⋆ f*y) , h.pres-⋆ _ _ ∙ ap₂ B._⋆_ p q
  image-subgroup .has-inv = ∥-∥-map λ where
    (f*x , p) → f*x A.⁻¹ , h.pres-inv _ ∙ ap B.inverse p

  im : Group ℓ
  im = _ , isSubgroup→GroupOn _ image-subgroup
```
