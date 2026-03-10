<!--
```agda
open import Cat.Displayed.Instances.Functor
open import Cat.Displayed.Reasoning as Dr
open import Cat.Displayed.Morphism as Dm
open import Cat.Functor.Naturality
open import Cat.Displayed.Functor
open import Cat.Displayed.Base
open import Cat.Reasoning as Cr
open import Cat.Prelude 
```
-->

```agda
module Cat.Displayed.Functor.Naturality where
```

# Natural isomorphisms of displayed categories {defines="displayed-natural-isomorphism"}

This module defines some displayed analogues of our [[natural isomorphism]]
machinery for ordinary category theory.

<!-- 
```agda
module _
  {oa ℓa ob ℓb oe ℓe of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf} 
  where
  private
    [ℰ,ℱ] = DisCat[ ℰ , ℱ ]
    module B = Cr B
    module ℰ where
      open Dr ℰ public
      open Dm ℰ public
    module ℱ where
      open Dr ℱ public
      open Dm ℱ public
    module [ℰ,ℱ] where
      open Dr [ℰ,ℱ] public
      open Dm [ℰ,ℱ] public
    
    variable 
      F G H : Functor A B
      α β : F => G
      a : ⌞ A ⌟
    
    open _=>_
    open _≅_
    open Inverses
    open Displayed-functor
    open _=[_]=>_
```
-->

```agda
  Inversesⁿ[_] : ∀ {F' : Displayed-functor F ℰ ℱ} {G' : Displayed-functor G ℰ ℱ}
    (inv : Inversesⁿ α β) → F' =[ α ]=> G' → G' =[ β ]=> F' → Type _
  Inversesⁿ[_] = [ℰ,ℱ].Inverses[_]

  is-invertibleⁿ[_] : ∀ {F' : Displayed-functor F ℰ ℱ} {G' : Displayed-functor G ℰ ℱ}
    (α-inv : is-invertibleⁿ α) (α' : F' =[ α ]=> G') → Type _
  is-invertibleⁿ[_] = [ℰ,ℱ].is-invertible[_]

  _≅ⁿ[_]_ : Displayed-functor F ℰ ℱ → F ≅ⁿ G → Displayed-functor G ℰ ℱ → Type _
  _≅ⁿ[_]_ = [ℰ,ℱ]._≅[_]_ 
```

We define combinators for basic operations on displayed natural
transformations:

```agda
  idni↓ : ∀ {F' : Displayed-functor F ℰ ℱ} → F' ≅ⁿ[ idni ] F'
  idni↓ = [ℰ,ℱ].id-iso↓

  _∘ni'_ 
    : ∀ {F' : Displayed-functor F ℰ ℱ} {G' : Displayed-functor G ℰ ℱ} 
      {H' : Displayed-functor H ℰ ℱ} {α β} 
    → G' ≅ⁿ[ β ] H' → F' ≅ⁿ[ α ] G' → F' ≅ⁿ[ β ∘ni α ] H'
  _∘ni'_ = [ℰ,ℱ]._∘Iso'_

  _∙ni'_
    : ∀ {F' : Displayed-functor F ℰ ℱ} {G' : Displayed-functor G ℰ ℱ} 
      {H' : Displayed-functor H ℰ ℱ} {α β} 
    → F' ≅ⁿ[ α ] G' → G' ≅ⁿ[ β ] H' → F' ≅ⁿ[ β ∘ni α ] H'
  α' ∙ni' β' = β' ∘ni' α'

  _ni⁻¹'
    : ∀ {α : F ≅ⁿ G} {F' : Displayed-functor F ℰ ℱ} {G' : Displayed-functor G ℰ ℱ} 
    → F' ≅ⁿ[ α ] G' → G' ≅ⁿ[ α ni⁻¹ ] F'
  _ni⁻¹' = [ℰ,ℱ]._Iso[]⁻¹

  infixr 30 _∘ni'_ _∙ni'_
  infix 31 _ni⁻¹'
```

If a natural transformation $\alpha' : F' \To G'$ is displayed over a 
natural isomorphism $\alpha : F \cong G$, then a family of inverses to
$\alpha'$ displayed over $\alpha^{-1}$ is automatically natural.

```agda
  inverse-is-natural[_]
    : ∀ {F' : Displayed-functor F ℰ ℱ} {G' : Displayed-functor G ℰ ℱ} (α : F ≅ⁿ G)
      (α' : F' =[ α .to ]=> G') 
      (β' : ∀ {a} (a' : ℰ.Ob[ a ]) →  ℱ.Hom[ α .from .η a ] (₀' G' a') (₀' F' a'))
    → (∀ {a} (a' : ℰ.Ob[ a ]) → α' .η' a' ℱ.∘' β' a'  ℱ.≡[ invl (inversesⁿ→inverses (inverses α) a) ] ℱ.id')
    → (∀ {a} (a' : ℰ.Ob[ a ]) → β' a' ℱ.∘' α' .η' a'  ℱ.≡[ invr (inversesⁿ→inverses (inverses α) a) ] ℱ.id')
    → is-natural-transformation[ α .from .is-natural ] G' F' β'
  inverse-is-natural[_] {F' = F'} {G'} α α' β' invl' invr' {x} {y} {f} x' y' f' = ℱ.begin[]
    β' y' ℱ.∘' ₁' G' f'                               ℱ.≡[]⟨ ℱ.refl⟩∘'⟨ ℱ.intror[] (invl (inversesⁿ→inverses (inverses α) x)) (invl' x') ⟩
    β' y' ℱ.∘' ₁' G' f' ℱ.∘' α' .η' x' ℱ.∘' β' x'     ℱ.≡[]˘⟨ ℱ.refl⟩∘'⟨ ℱ.extendl[] (α .to .is-natural x y f) (α' .is-natural' x' y' f') ⟩
    β' y' ℱ.∘' α' .η' y' ℱ.∘' ₁' F' f' ℱ.∘' β' x'     ℱ.≡[]⟨ ℱ.cancell[] (invr (inversesⁿ→inverses (inverses α) y)) (invr' y') ⟩
    ₁' F' f' ℱ.∘' β' x'                               ℱ.∎[]
```

Thus to define a displayed natural isomorphism, it suffices to give the
following data:

```agda
  record make-natural-iso[_] 
    (α : F ≅ⁿ G) (F' : Displayed-functor F ℰ ℱ) (G' : Displayed-functor G ℰ ℱ) 
    : Type (oa ⊔ ℓa ⊔ oe ⊔ ℓe ⊔ ℓf) where
    no-eta-equality
    
    private 
      module α = _=>_ (α .to)
      module α⁻¹ = _=>_ (α .from)

    field
      eta' : ∀ {x} (x' : ℰ.Ob[ x ]) → ℱ.Hom[ α.η x ] (₀' F' x') (₀' G' x')
      inv' : ∀ {x} (x' : ℰ.Ob[ x ]) → ℱ.Hom[ (α⁻¹.η x) ] (₀' G' x') (₀' F' x')
      eta'∘'inv' : ∀ {x} (x' : ℰ.Ob[ x ]) 
        → eta' x' ℱ.∘' inv' x' ℱ.≡[ inversesⁿ→inverses (inverses α) x .invl ] ℱ.id'
      inv'∘'eta' : ∀ {x} (x' : ℰ.Ob[ x ]) 
        → inv' x' ℱ.∘' eta' x' ℱ.≡[ inversesⁿ→inverses (inverses α) x .invr ] ℱ.id'
      natural : ∀ {x y f} (x' : ℰ.Ob[ x ]) (y' : ℰ.Ob[ y ]) (f' : ℰ.Hom[ f ] x' y') 
        → ₁' G' f' ℱ.∘' eta' x' ℱ.≡[ sym (α.is-natural x y f) ] eta' y' ℱ.∘' ₁' F' f'
    
  open make-natural-iso[_]

  to-natural-iso[] 
    : ∀ {α : F ≅ⁿ G} {F' : Displayed-functor F ℰ ℱ} {G' : Displayed-functor G ℰ ℱ}
    → make-natural-iso[ α ] F' G' → F' ≅ⁿ[ α ] G'
  {-# INLINE to-natural-iso[] #-}
  to-natural-iso[] {α = α} {F'} {G'} mk = 
    let to' = NT' (mk .eta') λ x' y' f' → symP (mk .natural x' y' f') in
    record 
      { to' = to' 
      ; from' = NT' (mk .inv') 
        (inverse-is-natural[ α ] to' (mk .inv') (mk .eta'∘'inv') (mk .inv'∘'eta')) 
      ; inverses' = record 
        { invl' = Nat'-path (mk .eta'∘'inv') 
        ; invr' = Nat'-path (mk .inv'∘'eta') } }
```

We also give the following helper functions:

```agda
  isoⁿ[]→iso[]
    : ∀ {α} {F' : Displayed-functor F ℰ ℱ} {G' : Displayed-functor G ℰ ℱ}
    → F' ≅ⁿ[ α ] G'
    → ∀ {a} (a' : ℰ.Ob[ a ]) → ₀' F' a' ℱ.≅[ (isoⁿ→iso α a) ] ₀' G' a'
  isoⁿ[]→iso[] α' a' = ℱ.make-iso[ _ ] (α' .to' .η' a') (α' .from' .η' a') (α' .invl' ηₚ' a') (α' .invr' ηₚ' a')

  to-is-invertibleⁿ[_]
    : ∀ {F' : Displayed-functor F ℰ ℱ} {G' : Displayed-functor G ℰ ℱ} 
      (α-invⁿ : is-invertibleⁿ α) 
      {α' : F' =[ α ]=> G'} (β' : G' =[ is-invertibleⁿ.inv α-invⁿ ]=> F')
    → (∀ {x} (x' : ℰ.Ob[ x ]) → α' .η' x' ℱ.∘' β' .η' x' 
      ℱ.≡[ is-invertibleⁿ→is-invertible α-invⁿ x .is-invertible.inverses .invl ] ℱ.id')
    → (∀ {x} (x' : ℰ.Ob[ x ]) → β' .η' x' ℱ.∘' α' .η' x' 
      ℱ.≡[ is-invertibleⁿ→is-invertible α-invⁿ x .is-invertible.inverses .invr ] ℱ.id')
    → is-invertibleⁿ[ α-invⁿ ] α'
  to-is-invertibleⁿ[ α-invⁿ ] β' p' q' = 
    [ℰ,ℱ].make-invertible[ α-invⁿ ] β' (Nat'-path p') (Nat'-path q')

  invertible[]→invertibleⁿ[_]
    : ∀ {F' : Displayed-functor F ℰ ℱ} {G' : Displayed-functor G ℰ ℱ} 
      (α-invⁿ : is-invertibleⁿ α) (α' : F' =[ α ]=> G')
    → (∀ {x} (x' : ℰ.Ob[ x ]) 
      → ℱ.is-invertible[ is-invertibleⁿ→is-invertible α-invⁿ x ] (α' .η' x'))
    → is-invertibleⁿ[ α-invⁿ ] α'
  invertible[]→invertibleⁿ[_] {F' = F'} {G'} α-invⁿ α' α'-invbl' 
    = to-is-invertibleⁿ[ α-invⁿ ] α'⁻¹ α'-invl' α'-invr' where
      α'-inv' : ∀ {x} (x' : ℰ.Ob[ x ]) → ℱ.Hom[ _ ] (₀' G' x') (₀' F' x')
      α'-inv' a' = α'-invbl' a' .is-invertible[_].inv'

      α'-invl' : ∀ {a} (a' : ℰ.Ob[ a ]) → α' .η' a' ℱ.∘' α'-inv' a' ℱ.≡[ _ ] ℱ.id'
      α'-invl' a' = α'-invbl' a' .is-invertible[_].inverses' .Inverses[_].invl'

      α'-invr' : ∀ {a} (a' : ℰ.Ob[ a ]) → α'-inv' a' ℱ.∘' α' .η' a' ℱ.≡[ _ ] ℱ.id'
      α'-invr' a' = α'-invbl' a' .is-invertible[_].inverses' .Inverses[_].invr'

      α'⁻¹ : _ =[ _ ]=> _
      α'⁻¹ = NT' α'-inv' (inverse-is-natural[ is-invertibleⁿ→isoⁿ α-invⁿ ] 
        α' α'-inv' α'-invl' α'-invr')
```
