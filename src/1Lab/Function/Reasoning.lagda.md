<!--
```agda
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module 1Lab.Function.Reasoning where
```

# Reasoning combinators for functions

Unlike for [paths] and [categories], reasoning about functions is often easy
because composition of functions is *strict*, i.e. definitionally unital
and associative.

[paths]: 1Lab.Path.Reasoning.html
[categories]: Cat.Reasoning.html

<!--
```agda
private variable
  ℓ : Level
  A B : Type ℓ
  f g h i : A → B
```
-->

## Notation

When doing equational reasoning, it's often somewhat clumsy to have to write
`ap (f ∘_) p` when proving that `f ∘ g ≡ f ∘ h`. To fix this, we steal
some cute mixfix notation from `agda-categories` which allows us to write
`≡⟨ refl⟩∘⟨ p ⟩` instead, which is much more aesthetically pleasing!

As unification is sometimes fiddly when functions are involved, we also
provide a way to write `≡⟨ f ∘⟨ p ⟩` instead.

```agda
_⟩∘⟨_ : f ≡ h → g ≡ i → f ∘ g ≡ h ∘ i
_⟩∘⟨_ = ap₂ (λ x y → x ∘ y)

refl⟩∘⟨_ : g ≡ h → f ∘ g ≡ f ∘ h
refl⟩∘⟨_ {f = f} p = ap (f ∘_) p

_⟩∘⟨refl : f ≡ h → f ∘ g ≡ h ∘ g
_⟩∘⟨refl {g = g} p = ap (_∘ g) p

_∘⟨_ : (f : A → B) → g ≡ h → f ∘ g ≡ f ∘ h
f ∘⟨ p = ap (f ∘_) p

_⟩∘_ : f ≡ h → (g : A → B) → f ∘ g ≡ h ∘ g
p ⟩∘ g = ap (_∘ g) p

infixr 39 _⟩∘⟨_ _∘⟨_ _⟩∘_
```
