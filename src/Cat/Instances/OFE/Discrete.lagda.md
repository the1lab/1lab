<!--
```agda
open import Cat.Instances.OFE
open import Cat.Prelude
```
-->

```agda
module Cat.Instances.OFE.Discrete where
```

# Discrete OFEs

Given a set $X$, we can make it into a **discrete [OFE]** by equipping
it with the relation that _takes one step_ to approximate equality: $x
\within{0} y$ is trivial, but $x \within{1 + n} y$ is defined to be $x =
y$, no matter what $n$ is.

[OFE]: Cat.Instances.OFE.html

```agda
Discrete-OFE : ∀ {ℓ} (A : Type ℓ) → is-set A → OFE-on ℓ A
Discrete-OFE A A-set .within zero x y = Lift _ ⊤
Discrete-OFE A A-set .within (suc n) x y = x ≡ y
Discrete-OFE A A-set .has-is-ofe .has-is-prop zero _ _ _ _ _ = _
Discrete-OFE A A-set .has-is-ofe .has-is-prop (suc n) = A-set

Discrete-OFE A A-set .has-is-ofe .≈-refl zero = _
Discrete-OFE A A-set .has-is-ofe .≈-refl (suc n) = refl

Discrete-OFE A A-set .has-is-ofe .≈-sym zero = _
Discrete-OFE A A-set .has-is-ofe .≈-sym (suc n) p = sym p

Discrete-OFE A A-set .has-is-ofe .≈-trans zero = _
Discrete-OFE A A-set .has-is-ofe .≈-trans (suc n) p q = q ∙ p

Discrete-OFE A A-set .has-is-ofe .bounded = _
Discrete-OFE A A-set .has-is-ofe .step zero = _
Discrete-OFE A A-set .has-is-ofe .step (suc n) x y p = p
Discrete-OFE A A-set .has-is-ofe .limit x y α = α 1
```
