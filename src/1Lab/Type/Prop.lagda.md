```agda
open import 1Lab.Equiv.FromPath
open import 1Lab.Univalence
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.Type.Prop where
```

# The (impredicative) universe of propositions

One result that Cubical Agda does _not_ let us conclude, which is handy
in the development of topos theory (and locale theory by extension), is
that [universes] of propositions are closed under arbitrary
quantification: If $P$ is a family of [propositions] at level $\ell$, but
$X : \ty\ \ell_2$, then $\prod_{(x : X)}P(x) : \ty\ (\ell_2 \sqcup
\ell)$ --- even though that dependent product has _at most one element_,
and so can not be a very large type at all.

[universes]: 1Lab.Type.html
[propositions]: 1Lab.HLevel.html#is-prop

We work around this using one of Agda's wildly unsafe features,
`NO_UNIVERSE_CHECK`. Like the name implies, it turns off universe
checking for a particular (group of) declarations --- which would
quickly lead to [inconsistency] when used without care.

[inconsistency]: 1Lab.Counterexamples.Russell.html

```agda
{-# NO_UNIVERSE_CHECK #-}
record Prop* : Type where
  field
    {ℓ} : Level
    ∣_∣ : Type ℓ
    is-tr : is-prop ∣_∣
open Prop* hiding (ℓ) public
```

The first thing we establish is a characterisation of paths in
`Prop*`{.Agda}, as is tradition. This definition is _also_ covered in
unsafety: Agda does not let us conclude that the types exist at the same
level simply from biimplication, so it needs to be convinced. Painfully.
With more than one postulate. Yikes.

```agda
prop-ua : ∀ {A B : Prop*} → (∣ A ∣ → ∣ B ∣) × (∣ B ∣ → ∣ A ∣) → A ≡ B
prop-ua {A} {B} (f , g) i = prop where
  -- Safe: we're ignoring the levels anyway.. These types are props!
  -- They're all at level zero! Begone, Agda.
  postulate levels : Path Level (A .Prop*.ℓ) (B .Prop*.ℓ)

  eqv : is-equiv g
  eqv .is-eqv y .centre = f y , A .is-tr _ _
  eqv .is-eqv y .paths (x , p) i = B .is-tr (f y) x i ,
    λ j → is-prop→squarep (λ i j → A .is-tr)
      (λ j → g (B .is-tr (f y) x j))
      (λ j → A .is-tr (g (f y)) y j) p (λ _ → y) i j

  path-of-types : (i : I) → Type (levels i)
  path-of-types i = Glue ∣ A ∣ λ where
    (i = i0) → ∣ A ∣ , id , id-equiv
    (i = i1) → ∣ B ∣ , g  , eqv

  -- Safe: is-prop is a prop, so any two of its values are equal. We
  -- can't use the standard methods here (is-prop-is-prop, etc) because
  -- you can't form PathPs over types with dependent levels.
  postulate
    trs : (i : I) → Sub (is-prop (path-of-types i)) (i ∨ ~ i)
      λ { (i = i0) → A .is-tr
        ; (i = i1) → B .is-tr
        }

  prop : Prop*
  prop .Prop*.ℓ = levels i
  prop .∣_∣     = path-of-types i
  prop .is-tr   = outS (trs i)

prop-ua-is-equiv : ∀ {A B} → is-equiv (prop-ua {A} {B})
prop-ua-is-equiv {A} {B} = is-iso→is-equiv (iso inverse isr isl) where
  inverse : ∀ {A B} → A ≡ B → (∣ A ∣ → ∣ B ∣) × (∣ B ∣ → ∣ A ∣)
  inverse p = transp (λ i → ∣ p i ∣) i0 , transp (λ i → ∣ p (~ i) ∣) i0

  isr : ∀ {A B} → is-right-inverse (inverse {A} {B}) prop-ua
  isr {A} = J (λ y p → prop-ua (inverse p) ≡ p) prop-ua-id-equiv where postulate
    -- Safe: ua (transport refl) ≡ refl, the other two components don't
    -- matter. Can't show this because of the "levels" and "trs"
    -- postulates.
    prop-ua-id-equiv : ∀ {A} → prop-ua {A} (transport refl , transport refl) ≡ refl

  isl : is-left-inverse (inverse {A} {B}) prop-ua
  isl x = Σ-pathp
    (funext (λ _ → B .is-tr _ _))
    (funext (λ _ → A .is-tr _ _))
```
