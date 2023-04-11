```agda
open import Cat.Instances.Shape.Interval using (Arr)
open import Cat.Displayed.Composition
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Functor
open import Cat.Displayed.Adjoint
open import Cat.Displayed.Base
open import Cat.Instances.Slice
open import Cat.Prelude

module Cat.Displayed.InternalSum
  {o ℓ o′ ℓ′} {B : Precategory o ℓ} (E : Displayed B o′ ℓ′)  where

open Precategory B
open Displayed E

open import Cat.Diagram.Pullback B
```

# Internal sums

One can describe the property of a [category][cat] to have sums as
a purley fibrational property. This property can then be used to define
what it shall mean that a [displayed category][disp] has **internal sums**.

More precise let $\cB$ a category with pullbacks and $E$ a displayed
category over $\cB$. We say $E$ has internal sums if
$η_E : \mathrm{Fam}(E) → E$ has a [fibered left adjoint][disadj] $\coprod_E$.

[cat]: Cat.Base.html
[disp]: Cat.Displayed.Base.html
[disadj]: Cat.Displayed.Adjoint.html

```agda
module _ (BhasPB : has-pullbacks) where
  open import Cat.Displayed.Instances.Slice B
  open import Cat.Displayed.Total
```

Therefore we first have to define the [fibred functor][disfunc]
$\eta_E : \mathrm{Fam}(E) → E$ as in the diagram

[disfunc]: Cat.Displayed.Functor.html

~~~{.quiver}
\[\begin{tikzcd}
	E \\
	& {E\downarrow \mathcal B} & E \\
	{\mathcal B} & {\mathcal B^2} & {\mathcal B} \\
	& {\mathcal B}
	\arrow[from=2-2, to=2-3]
	\arrow[category over, from=2-3, to=3-3]
	\arrow[category over, from=2-2, to=3-2]
	\arrow["{\mathrm{dom}}"', from=3-2, to=3-3]
	\arrow["{\mathrm{cod}}", from=3-2, to=4-2]
	\arrow["{\eta_E}"', dashed, from=1-1, to=2-2]
	\arrow[category over, from=1-1, to=3-1]
	\arrow["{\Delta_\mathcal B}", from=3-1, to=3-2]
	\arrow["{\mathrm{id}_E}"{description}, from=1-1, to=2-3]
	\arrow["{\mathrm{id}_\mathcal B }"{description}, from=3-1, to=4-2]
	\arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=2-2, to=3-3]
\end{tikzcd}\]
~~~

where $\cB^2$ is the arrow category of $\cB$ whose objects are morphisms
$a → b$ from $\cB$,

```agda
  B² : Precategory (o ⊔ ℓ) (o ⊔ ℓ)
  B² = ∫ Slices
```

$\mathrm{dom} : \cB^2 → \cB$ is the domain functor, sending an object
$a → b$ in $\cB^2$ to $a$.

```agda
  dom : Functor B² B
  dom .Functor.F₀ x = (x .snd) ./-Obj.domain
  dom .Functor.F₁ f = ( f .Total-hom.preserves) .Slice-hom.to
  dom .Functor.F-id = refl
  dom .Functor.F-∘ f g = refl
```

Now $E↓\cB$ is the [pullback of the displayed category][disppb] $E$
along $\mathrm{dom}

[disppb]: Cat.Displayed.Instances.Pullback.html

```agda
  open import Cat.Displayed.Instances.Pullback dom E
  
  E↓B : Displayed B² o′  ℓ′
  E↓B = Change-of-base
```

and $\mathrm{Fam}$ is the [composition of the displayed categories][comp]
`Slices` (see [here][slice]) and $E↓\cB$. 

[comp]: Cat.Displayed.Composition.html
[slice]: Cat.Displayed.Instances.Slice.html

```agda
  Fam : Displayed B (o ⊔ ℓ ⊔ o′) (o ⊔ ℓ ⊔ ℓ′)
  Fam =  Slices D∘ E↓B
```

One can easily check that $η_E$ from the diagram above, given by the
universal property of pullbacks can be explicitly defined as follows:

```agda
  import Cat.Reasoning B as CR

  ηE : Displayed-functor E Fam Id
  ηE .Displayed-functor.F₀′ {b} x .fst ./-Obj.domain = b
  ηE .Displayed-functor.F₀′ x .fst ./-Obj.map = id
  ηE .Displayed-functor.F₀′ x .snd = x
  ηE .Displayed-functor.F₁′ {f = f} f′ .fst = slice-hom f CR.id-comm
  ηE .Displayed-functor.F₁′ f′ .snd = f′
  ηE .Displayed-functor.F-id′ = Σ-path (Slice-pathp refl refl) refl
  ηE .Displayed-functor.F-∘′ = Σ-path (Slice-pathp refl refl) refl
```

This defines a fibred functor from $E$ to $\mathrm{Fam}$.
```agda
  ηE-fib : Fibred-functor E Fam Id
  ηE-fib .Fibred-functor.disp = ηE
  ηE-fib .Fibred-functor.F-cartesian {a = a} {a′ = a′} {b′ = b′} {f = f} f′ f′-cart
    = ηf′-cart where
    module ηE = Displayed-functor ηE
    module f′ = is-cartesian f′-cart
    module E↓B = Displayed E↓B
    module Fam = Displayed Fam
    module E = Displayed E
    open import Cat.Displayed.Reasoning E
    
    φ : {u : CR.Ob} {u′ : Fam.Ob[ u ]} (m : CR.Hom u a)
         (h′ : Fam.Hom[ f ∘ m ] u′ (ηE.F₀′ b′))
       → E.Hom[ m ∘ u′ .fst ./-Obj.map ] (u′ .snd) a′
    φ {u′ = u′} m h′
      = f′.universal (m ∘ u′ .fst ./-Obj.map)
         (hom[ CR.assoc _ _ _ ∙ h′ .fst .Slice-hom.commute ∙ CR.idl _ ]⁻ (h′ .snd)) 
    ηf′-cart : is-cartesian Fam f (ηE.₁′ f′)
    ηf′-cart .is-cartesian.universal {u′ = u′} m h′
      = slice-hom (m ∘ u′ .fst ./-Obj.map) (sym (CR.idl _)) , φ m h′
    ηf′-cart .is-cartesian.commutes {u′ = u′} m h′
      = Σ-path (Slice-pathp refl
         (CR.assoc _ _ _ ∙ h′ .fst .Slice-hom.commute ∙ CR.idl _))
         (hom[ CR.assoc _ _ _ ∙ h′ .fst .Slice-hom.commute ∙ CR.idl _ ]
           ((ηE.₁′ f′ Fam.∘′ ηf′-cart .is-cartesian.universal m h′) .snd) ≡⟨ hom[]⟩⟨ refl ⟩
         hom[ CR.assoc _ _ _ ∙ h′ .fst .Slice-hom.commute ∙ CR.idl _ ]
           (hom[ refl ] (ηE.₁′ f′ .snd E.∘′ ηf′-cart .is-cartesian.universal m h′ .snd)) ≡⟨ hom[]⟩⟨ liberate _ ⟩
         hom[ CR.assoc _ _ _ ∙ h′ .fst .Slice-hom.commute ∙ CR.idl _ ]
           (ηE.₁′ f′ .snd E.∘′ ηf′-cart .is-cartesian.universal m h′ .snd) ≡⟨ hom[]⟩⟨ refl ⟩
         hom[ CR.assoc _ _ _ ∙ h′ .fst .Slice-hom.commute ∙ CR.idl _ ]
           (f′ E.∘′ φ m h′) ≡⟨ (hom[]⟩⟨ com) ∙ hom[]-∙ _ _ ∙ liberate _ ⟩
         h′ .snd ∎) where
      com : _
      com = f′.commutes (m ∘ u′ .fst ./-Obj.map)
                 (hom[ CR.assoc _ _ _ ∙ h′ .fst .Slice-hom.commute ∙ CR.idl _ ]⁻ (h′ .snd))
    ηf′-cart .is-cartesian.unique {u′ = u′} {m = m} {h′ = h′} m′ f′m′≡h′
      = Σ-path (Slice-pathp refl (sym (m′ .fst .Slice-hom.commute ∙ CR.idl _))) uniq
      where
      uniq : hom[ m′ .fst .Slice-hom.commute ∙ CR.idl _ ]⁻ (m′ .snd) ≡ φ m h′
      uniq = f′.unique (hom[ m′ .fst .Slice-hom.commute ∙ CR.idl _ ]⁻ (m′ .snd))
        (f′ E.∘′ hom[ m′ .fst .Slice-hom.commute ∙ CR.idl _ ]⁻ (m′ .snd) ≡⟨ whisker-r _ ⟩
        hom[ ap (f ∘_) (m′ .fst .Slice-hom.commute ∙ CR.idl _) ]⁻ (f′ E.∘′ m′ .snd) ≡˘⟨ hom[]⟩⟨ liberate _ ⟩
        hom[ ap (f ∘_) (m′ .fst .Slice-hom.commute ∙ CR.idl _) ]⁻
          (hom[ refl ] (f′ E.∘′ m′ .snd)) ≡⟨ hom[]⟩⟨ refl ⟩
        hom[ ap (f ∘_) (m′ .fst .Slice-hom.commute ∙ CR.idl _) ]⁻
          ((ηE.₁′ f′ Fam.∘′ m′) .snd) ≡⟨ hom[]⟩⟨ from-pathp⁻ (ap (λ x → x .snd) f′m′≡h′) ⟩
        hom[ ap (f ∘_) (m′ .fst .Slice-hom.commute ∙ CR.idl _) ]⁻
          (hom[ ap (λ x → x .fst .Slice-hom.to) f′m′≡h′ ]⁻ (h′ .snd)) ≡⟨ hom[]-∙ _ _ ∙ reindex _ _ ⟩
        hom[ CR.assoc _ _ _ ∙ h′ .fst .Slice-hom.commute ∙ CR.idl _ ]⁻ (h′ .snd) ∎) 
```

Finally we can give the definition that $E$ has internal sums
```agda
  η-fib : Fibred-functor-single-base E Fam
  η-fib = Fibred-functor-over-id→over-single-base ηE-fib

  record InternalSum : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′)
    where
    no-eta-equality
    field
      ∐ : Fibred-functor-single-base Fam E
      adjunction : ∐ ⊣′ η-fib
```
