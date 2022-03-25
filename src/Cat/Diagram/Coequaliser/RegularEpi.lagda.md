```agda
open import Cat.Diagram.Coequaliser
open import Cat.Diagram.Pullback
open import Cat.Diagram.Initial
open import Cat.Prelude

import Cat.Reasoning

module Cat.Diagram.Coequaliser.RegularEpi {o ℓ} (C : Precategory o ℓ) where
```

<!--
```agda
open Cat.Reasoning C
private variable a b : Ob
```
-->

# Regular epimorphisms

[Dually] to [regular monomorphisms], which behave as _embeddings_,
regular [epimorphisms] behave like _covers_: A regular epimorphism $f :
a \epi b$ expresses $b$ as "a union of parts of $a$, possibly glued
together".

[Dually]: Cat.Base.html#opposites
[regular monomorphisms]: Cat.Diagram.Equaliser.RegularMono.html
[epimorphisms]: Cat.Morphism.html#epis

The definition is also precisely dual: A map $f : a \to b$ is a
**regular epimorphism** if it is the [coequaliser] of some pair of
arrows $R \rightrightarrows a$.

[coequaliser]: Cat.Diagram.Coequaliser.html

```agda
record is-regular-epi (f : Hom a b) : Type (o ⊔ ℓ) where
  no-eta-equality
  constructor reg-epi
  field
    {r}           : Ob
    {arr₁} {arr₂} : Hom r a
    has-is-coeq   : is-coequaliser C arr₁ arr₂ f

  open is-coequaliser has-is-coeq public
```

From the definition we can directly conclude that regular epis are in
fact epic:

```agda
  is-regular-epi→is-epic : is-epic f
  is-regular-epi→is-epic = is-coequaliser→is-epic C _ has-is-coeq

open is-regular-epi using (is-regular-epi→is-epic) public
```

## Effective epis

Again by duality, we have a pair of canonical choices of maps which $f$
may coequalise: Its _kernel pair_, that is, the [pullback] of $f$ along
itself. An epimorphism which coequalises its kernel pair is called an
**effective epi**, and effective epis are immediately seen to be regular
epis:

[pullback]: Cat.Diagram.Pullback.html

```agda
record is-effective-epi (f : Hom a b) : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    {kernel}       : Ob
    p₁ p₂          : Hom kernel a
    is-kernel-pair : is-pullback C p₁ f p₂ f
    has-is-coeq    : is-coequaliser C p₁ p₂ f

  is-effective-epi→is-regular-epi : is-regular-epi f
  is-effective-epi→is-regular-epi = re where
    open is-regular-epi hiding (has-is-coeq)
    re : is-regular-epi f
    re .r = _
    re .arr₁ = _
    re .arr₂ = _
    re .is-regular-epi.has-is-coeq = has-is-coeq
```

If a regular epimorphism (a coequaliser) has a kernel pair, then it is
also the coequaliser of its kernel pair. That is: If the pullback of $a
\xto{f} b \xot{f} a$ exists, then $f$ is also an effective epimorphism.

```agda
is-regular-epi→is-effective-epi
  : ∀ {a b} {f : Hom a b}
  → Pullback C f f
  → is-regular-epi f
  → is-effective-epi f
is-regular-epi→is-effective-epi {f = f} kp reg = eff where
  module reg = is-regular-epi reg
  module kp = Pullback kp

  open is-effective-epi
  open is-coequaliser
  eff : is-effective-epi f
  eff .kernel = kp.apex
  eff .p₁ = kp.p₁
  eff .p₂ = kp.p₂
  eff .is-kernel-pair = kp.has-is-pb
  eff .has-is-coeq .coequal = kp.square
  eff .has-is-coeq .coequalise {F = F} {e′} p = reg.coequalise q where
    q : e′ ∘ reg.arr₁ ≡ e′ ∘ reg.arr₂
    q =
      e′ ∘ reg.arr₁                               ≡⟨ ap (e′ ∘_) (sym kp.p₂∘limiting) ⟩
      e′ ∘ kp.p₂ ∘ kp.limiting (sym reg.coequal)  ≡⟨ pulll (sym p) ⟩
      (e′ ∘ kp.p₁) ∘ kp.limiting _                ≡⟨ pullr kp.p₁∘limiting ⟩
      e′ ∘ reg.arr₂                               ∎
  eff .has-is-coeq .universal = reg.universal
  eff .has-is-coeq .unique = reg.unique
```
