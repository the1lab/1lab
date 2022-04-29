<!--
```agda
open import Cat.Diagram.Limit.Finite
open import Cat.Prelude hiding (_-_)
open import Cat.Abelian.Base
```
-->

```agda
module Cat.Abelian.Limits {o ℓ} {C : Precategory o ℓ} (A : is-pre-abelian C) where
open is-pre-abelian A
```

# Limits

Recall that every [pre-abelian] admits [kernels] and cokernels, and is
also [additive], so it additionally has products and
coproducts^[actually, they're the same thing!]. It sounds like we're
missing some [finite limits] (dually, missing some finite colimits), but
it turns out that this is enough: We can construct the [equaliser] of
$f, g : A \to B$ as $\ker(f - g)$ --- whence the name **difference
kernel**!

[abelian]: Cat.Abelian.Base.html#pre-abelian-abelian-categories
[pre-abelian]: Cat.Abelian.Base.html#pre-abelian-abelian-categories
[kernels]: Cat.Diagram.Kernel.html
[additive]: Cat.Abelian.Base.html#additive-categories
[equaliser]: Cat.Diagram.Equaliser.html
[finite limits]: Cat.Diagram.Limit.Finite.html

The calculation is straightforward: To map out of $\ker f$, we must have
$(fe' - ge') = 0$, but this is immediate assuming that $fe' = ge'$ ---
an assumption we _have_ to map out of $\id{eq}(f,g)$.  Similarly, to
show that $f\ker(f-g) = g\ker(f-g)$, we calculate

$$
f\ker(f-g) - g\ker(f-g) = (f-g)\ker(f-g) = 0\text{.}
$$

```agda
difference-kernel
  : ∀ {A B} {f g : Hom A B}
  → is-equaliser f g (Ker.kernel (f - g))
difference-kernel {f = f} {g} = equ where
  open is-equaliser
  equ : is-equaliser f g (Ker.kernel (f - g))
  equ .equal = zero-diff $
    (f ∘ Ker.kernel (f - g)) - (g ∘ Ker.kernel (f - g)) ≡⟨ ∘-minus-l f g (Ker.kernel (f - g)) ⟩
    (f - g) ∘ Ker.kernel (f - g)                        ≡⟨ Ker.equal (f - g) ⟩
    ∅.zero→ ∘ Ker.kernel (f - g)                        ≡⟨ ∅.zero-∘r _ ∙ 0m-unique ⟩
    0m                                                  ∎
  equ .limiting {e′ = e′} p = Ker.limiting (f - g) {e′ = e′} $
    (f - g) ∘ e′         ≡˘⟨ ∘-minus-l _ _ _ ⟩
    f ∘ e′ - g ∘ e′      ≡⟨ ap (f ∘ e′ -_) (sym p) ⟩
    f ∘ e′ - f ∘ e′      ≡⟨ Hom.inverser ⟩
    0m                   ≡˘⟨ ∅.zero-∘r _ ∙ 0m-unique ⟩
    Zero.zero→ ∅ ∘ e′    ∎
  equ .universal = Ker.universal _
  equ .unique = Ker.unique (f - g)
```

By a standard characterisation of finite limits in terms of finite
products and binary equalisers, the construction of "difference kernels"
above implies that any pre-abelian category is finitely complete.

```agda
finitely-complete : Finitely-complete C
finitely-complete =
  with-equalisers C has-terminal has-prods λ f g →
    record { has-is-eq = difference-kernel }
```
