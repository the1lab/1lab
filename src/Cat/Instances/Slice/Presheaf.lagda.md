<!--
```agda
open import Cat.Functor.Equivalence
open import Cat.Functor.Properties
open import Cat.Instances.Elements
open import Cat.Instances.Slice
open import Cat.Functor.Base
open import Cat.Functor.Hom
open import Cat.Prelude
```
-->

```agda
module Cat.Instances.Slice.Presheaf {o ℓ} {C : Precategory o ℓ} where
```

# Slices of presheaf categories

We prove that slices of a presheaf category are again presheaf
categories. Specifically, for $P$ a presheaf, we have an isomorphism
$\psh(\cC)/P \cong \psh(\int P)$, where $\int$ denotes the [category
of elements] of $P$.

[category of elements]: Cat.Instances.Elements.html

<!--
```agda
private
  variable κ : Level
  module C = Precategory C
open Precategory
open Element-hom
open Functor
open /-Obj
open /-Hom
open _=>_
```
-->

An object in the slice $\psh(\cC)/P$ consists of a functor $Q$
together with a natural transformation $\eta : P \to Q$. To transform
this data into a functor $\int P \to \Sets$, observe that for each
element $(x, s)$ in $\int P$, the fibre $\eta_x^*(s)$ is a set. But why
this choice in particular? Well, observe that $\int P$ is essentially
the _total space_ of $P$ --- so that what we're doing here is proving an
equivalence between fibrations and dependent functions! This is in line
with the existence of [object classifiers], and in the 1-categorical
level, with [slices of Sets].

[object classifiers]: 1Lab.Univalence.html#object-classifiers
[slices of Sets]: Cat.Instances.Slice.html#slices-of-sets

In fact, since we have $\Sets = \psh(*)$, that latter equivalence is a
special case of the one constructed here --- where in the calculation
below, $c$ denotes the constant presheaf $* \mapsto S$. The category of
elements of a presheaf $* \mapsto S$ consists of pairs $(x, e)$ where $x
: *$, of which there is only one choice, and $e : S$.

$$
\Sets/S \cong \psh(*)/c(S) \cong \psh(\textstyle\int c(S)) \cong \psh(\rm{Disc}(S))
$$

```agda
module _ {P : Functor (C ^op) (Sets κ)} where
  private module P = Functor P

  slice-ob→presheaf
    : Ob (Slice Cat[ C ^op , Sets κ ] P)
    → Functor (∫ C P ^op) (Sets κ)
  slice-ob→presheaf sl .F₀ (elem x s) = el! (fibre (sl .map .η x) s)

  slice-ob→presheaf sl .F₁ eh (i , p) =
      sl .dom .F₁ (eh .hom) i
    , happly (sl .map .is-natural _ _ _) _ ∙∙ ap (P.₁ _) p ∙∙ eh .commute
```

<!--
```agda
  slice-ob→presheaf sl .F-id =
    funext λ x → Σ-prop-path! (happly (sl .dom .F-id) _)
  slice-ob→presheaf sl .F-∘ f g =
    funext λ x → Σ-prop-path! (happly (sl .dom .F-∘ _ _) _)

  private abstract
    lemma
      : ∀ (y : Functor (∫ C P ^op) (Sets κ))
          {o o'} {s} {s'} {el : y ʻ (elem o s)}
          {f : C .Hom o' o} (p : P .F₁ f s ≡ s')
      → subst (λ e → y ʻ elem o' e) p (y .F₁ (elem-hom f refl) el)
      ≡ y .F₁ (elem-hom f p) el
    lemma y {o = o} {o' = o'} {el = it} {f = f} =
      J (λ s' p → subst (λ e → y ʻ (elem o' e)) p (y .F₁ (elem-hom f refl) it)
                ≡ y .F₁ (elem-hom f p) it)
        (transport-refl _)
```
-->

Keeping with the theme, in the other direction, we take a total space
rather than a family of fibres, with fibration being the first
projection `fst`{.Agda}:

```agda
  presheaf→slice-ob : Functor (∫ C P ^op) (Sets κ) → Ob (Slice Cat[ C ^op , Sets κ ] P)
  presheaf→slice-ob y = obj where
    obj : /-Obj {C = Cat[ _ , _ ]} P
    obj .dom .F₀ c .∣_∣   = Σ[ sect ∈ P ʻ c ] y ʻ elem c sect
    obj .dom .F₀ c .is-tr = hlevel 2
    obj .dom .F₁ f (x , p) = P.₁ f x , y .F₁ (elem-hom f refl) p
    obj .map .η x = fst
```

<!--
```agda
    obj .dom .F-id {ob} = funext λ { (x , p) → Σ-path (happly (P.F-id) x) (lemma y _ ∙ happly (y .F-id) _) }
    obj .dom .F-∘ f g = funext λ { (x , p) →
      Σ-path (happly (P.F-∘ f g) x)
        ( lemma y _
        ∙∙ ap (λ e → y .F₁ (elem-hom (g C.∘ f) e) p) (P.₀ _ .is-tr _ _ _ _)
        ∙∙ happly (y .F-∘ (elem-hom f refl) (elem-hom g refl)) _) }
    obj .map .is-natural _ _ _ = refl
```
-->

Since the rest of the construction is routine calculation, we present it
without comment.

```agda
  slice→total : Functor (Slice Cat[ C ^op , Sets κ ] P) Cat[ (∫ C P) ^op , Sets κ ]
  slice→total = func where
    func : Functor (Slice Cat[ C ^op , Sets κ ] P) Cat[ (∫ C P) ^op , Sets κ ]
    func .F₀ = slice-ob→presheaf
    func .F₁ {x} {y} h .η i arg =
      h .map .η (i .fst) (arg .fst) , h .com ηₚ _ $ₚ arg .fst ∙ arg .snd
    func .F₁ {x} {y} h .is-natural _ _ _ = funext λ i →
      Σ-prop-path! (happly (h .map .is-natural _ _ _) _)

    func .F-id    = ext λ x y p → Σ-prop-path! refl
    func .F-∘ f g = ext λ x y p → Σ-prop-path! refl

  slice→total-is-ff : is-fully-faithful slice→total
  slice→total-is-ff {x} {y} = is-iso→is-equiv (iso inv rinv linv) where
    inv : Hom Cat[ ∫ C P ^op , Sets _ ] _ _
        → Slice Cat[ C ^op , Sets _ ] P .Hom _ _
    inv nt .map .η i o = nt .η (elem _ (x .map .η i o)) (o , refl) .fst

    inv nt .map .is-natural _ _ f = funext λ z →
        ap (λ e → nt .η _ e .fst) (Σ-prop-path! refl)
      ∙ ap fst (happly (nt .is-natural _ _
          (elem-hom f (happly (sym (x .map .is-natural _ _ _)) _))) _)

    inv nt .com = ext λ z w →
      nt .η (elem _ (x .map .η _ _)) (w , refl) .snd

    rinv : is-right-inverse inv (F₁ slice→total)
    rinv nt = ext λ where
      o z p → Σ-prop-path! λ i →
        nt .η (elem (o .fst) (p i)) (z , λ j → p (i ∧ j)) .fst

    linv : is-left-inverse inv (F₁ slice→total)
    linv sh = ext λ _ _ → refl

  open is-precat-iso
  slice→total-is-iso : is-precat-iso slice→total
  slice→total-is-iso .has-is-ff = slice→total-is-ff
  slice→total-is-iso .has-is-iso = is-iso→is-equiv isom where
    open is-iso
    isom : is-iso slice-ob→presheaf
    isom .from = presheaf→slice-ob
```

Proving that the constructions `presheaf→slice-ob`{.Agda} and
`slice-ob→presheaf`{.Agda} are inverses is mosly incredibly fiddly path
algebra, so we omit the proof.

<!--
```agda
    isom .rinv x =
      Functor-path
        (λ i → n-ua (Fibre-equiv (λ a → x ʻ elem (i .fst) a) (i .snd)))
        λ f → ua→ λ { ((a , b) , p) → path→ua-pathp _ (lemma x _ ∙ lemma' _ _ _) }
      where abstract
        lemma'
          : ∀ {o o'} {sect : P ʻ o .fst}
              (f : Hom (∫ C P ^op) o o')
              (b : x ʻ elem (o .fst) sect)
              (p : sect ≡ o .snd)
          → x .F₁ (elem-hom (f .hom) (ap (P.₁ (f .hom)) p ∙ f .commute)) b
          ≡ x .F₁ f (subst (λ e → x ʻ elem (o .fst) e) p b)
        lemma' {o = o} {o' = o'} f b p =
          J (λ _ p → ∀ f b → x .F₁ (elem-hom (f .hom) (ap (P.₁ (f .hom)) p ∙ f .commute)) b
                           ≡ x .F₁ f (subst (λ e → x ʻ elem (o .fst) e) p b))
            (λ f b → ap₂ (x .F₁) (ext refl) (sym (transport-refl b)))
            p f b

    isom .linv x =
      /-Obj-path
        (Functor-path (λ x → n-ua (Total-equiv _ e⁻¹))
          λ f → ua→ λ a → path→ua-pathp _ refl)
        (Nat-pathp _ _ (λ x → ua→ (λ x → sym (x .snd .snd))))

  -- downgrade to an equivalence for continuity/cocontinuity
  slice→total-is-equiv : is-equivalence slice→total
  slice→total-is-equiv = is-precat-iso→is-equivalence slice→total-is-iso

  total→slice : Functor Cat[ (∫ C P) ^op , Sets κ ] (Slice Cat[ C ^op , Sets κ ] P)
  total→slice = slice→total-is-equiv .is-equivalence.F⁻¹
```
-->
