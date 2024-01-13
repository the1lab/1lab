<!--
```agda
open import Algebra.Group.NAry
open import Algebra.Group.Ab

open import Cat.Diagram.Coproduct.Indexed
open import Cat.Diagram.Product.Indexed
open import Cat.Diagram.Limit.Finite
open import Cat.Abelian.Base
open import Cat.Prelude hiding (_-_ ; _+_)

open import Data.Id.Base
open import Data.Dec
open import Data.Fin

import Cat.Abelian.NAry
```
-->

```agda
module Cat.Abelian.Limits {o ℓ} {C : Precategory o ℓ} where
```

# Limits

Recall that every [pre-abelian] category admits [kernels] and cokernels,
and is also [additive], so it additionally has products and
coproducts^[We'll see in this very same module that they're actually the
same thing!]. It sounds like we're missing some [[finite limits]] (dually,
missing some finite colimits), but it turns out that this is enough: We
can construct the [[equaliser]] of $f, g : A \to B$ as $\ker(f - g)$ ---
whence the name **difference kernel**!

[abelian]: Cat.Abelian.Base.html#pre-abelian-abelian-categories
[pre-abelian]: Cat.Abelian.Base.html#pre-abelian-abelian-categories
[kernels]: Cat.Diagram.Equaliser.Kernel.html
[additive]: Cat.Abelian.Base.html#additive-categories

The calculation is straightforward: To map out of $\ker f$, we must have
$(fe' - ge') = 0$, but this is immediate assuming that $fe' = ge'$ ---
an assumption we _have_ to map out of $\rm{eq}(f,g)$.  Similarly, to
show that $f\ker(f-g) = g\ker(f-g)$, we calculate

$$
f\ker(f-g) - g\ker(f-g) = (f-g)\ker(f-g) = 0\text{.}
$$

```agda
module _ (A : is-pre-abelian C) where
  open is-pre-abelian A
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
    equ .universal {e' = e'} p = Ker.universal (f - g) {e' = e'} $
      (f - g) ∘ e'         ≡˘⟨ ∘-minus-l _ _ _ ⟩
      f ∘ e' - g ∘ e'      ≡⟨ ap (f ∘ e' -_) (sym p) ⟩
      f ∘ e' - f ∘ e'      ≡⟨ Hom.inverser ⟩
      0m                   ≡˘⟨ ∅.zero-∘r _ ∙ 0m-unique ⟩
      Zero.zero→ ∅ ∘ e'    ∎
    equ .factors = Ker.factors _
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

## Finite biproducts

An interesting property of $\Ab$-enriched categories is the coincidence
of finite products and finite coproducts: not only is there a map^[In
the binary case.] $a \sqcup b \to a \times b$, defined from the
universal properties, but it is also an isomorphism.  This is, at least
to the author, mildly unexpected, but it follows from the properties of
zero morphisms.

More generally, suppose that $F : [n] \to \cA$ is a finite family of
objects in an $\Ab$-category. If $F$ has both a coproduct $\coprod F$
and a product $\prod F$ in $\cA$, then we can define a map $\coprod F
\to \prod F$ by giving a family of morphisms $F_i \to \prod F$, which
amounts to defining a family of morphisms $F_i \to F_j$^[Where $i, j$
both range over $[n]$.]. Since $[n]$ is discrete, we can define this
family to be $\id : F_i \to F_i$ when $i = j$ and $0 : F_i \to F_j$
everywhere else!

What we actually prove in this module is a slight variation: we directly
construct, given a product $\prod F$, the structure of a coproduct _on
$\prod F$_. Uniqueness of coproducts then implies that, if some other
$\coprod F$ exists, then it must be isomorphic to $\coprod F$.

<!--
```agda
module _ (A : Ab-category C) {I : Nat} (F : Fin I → C .Precategory.Ob)
         (ip : Indexed-product C F) where
  private
    module A = Ab-category A
    module ip = Indexed-product ip
  open Cat.Abelian.NAry A
```
-->

The first thing we'll prove is a compatibility condition between tupling
and sums: A sum of tuples is a tuple of sums. In the binary case, we're
showing that $(a, b) + (c, d)$ is $(a + c, b + d)$.

```agda
  tuple-sum : ∀ {j} {R} (f : Fin j → ∀ i → A.Hom R (F i))
        → ip.tuple (λ i → ∑ₕ j (λ j → f j i))
        ≡ ∑ₕ j λ j → ip.tuple (f j)
  tuple-sum {j} f = sym $ ip.unique _ λ i →
    ip.π i A.∘ ∑ₕ j (λ i → ip.tuple (f i))   ≡⟨ ∑-∘-left {j = j} _ ⟩
    ∑ₕ j (λ j → ip.π i A.∘ ip.tuple (f j))   ≡⟨ ∑-path {j} _ (λ j → ip.commute) ⟩
    ∑ₕ j (λ j → f j i)                       ∎
```

We then define our function $\delta_{i,j} : F_i \to F_j$ which is the
identity on the diagonal.

```agda
  private
    δ' : (i j : Fin I) → Dec (i ≡ᵢ j) → A.Hom (F i) (F j)
    δ' i j (yes reflᵢ) = A.id
    δ' i j (no x) = A.0m

    δ : ∀ i j → A.Hom (F i) (F j)
    δ i j = δ' i j (i ≡ᵢ? j)

    δᵢⱼ : ∀ i j → ¬ i ≡ j → (d : Dec (i ≡ᵢ j)) → δ' i j d ≡ A.0m
    δᵢⱼ i j i≠j (yes i=j) = absurd (i≠j (Id≃path.to i=j))
    δᵢⱼ i j i≠j (no _)    = refl
```

We can now define a factoring of the identity on $\prod F$ through a ---
hypothetical --- $\coprod F$. A "splitting" map $\prod F \to \prod F$,
which works by summing (over $j$) the tupling (over $i$) of
$\delta_{i,j}\pi_j$; and since tupling commutes with sums, we conclude
that this is the tupling over $i$ of a bunch of tuples, zero on every
component _except_ for the one corresponding to their index in the sum.
In the binary case, we're showing that

$$
(1, 0)\pi_1 + (0,1)\pi_2 = (\pi_1, 0) + (0, \pi_2) = (\pi_1, \pi_2) = \id\text{.}
$$

```agda
  split = ∑ₕ I λ j → ip.tuple λ i → δ j i A.∘ ip.π j

  private
    split-remark : A.id ≡ split
    split-remark = ip.unique ip.π (λ _ → A.idr _) ∙ sym (ip.unique _ πΣδπ) where
      sum-δ-π : ∀ i → ∑ {I} _ (λ j → δ j i A.∘ ip.π j) ≡ ip.π i
      sum-δ-π i = ∑-diagonal-lemma (Abelian→Group-on (A.Abelian-group-on-hom _ _)) {I} i _
        (A.eliml refl) λ j i≠j →
          ap₂ A._∘_ (δᵢⱼ j i (λ e → i≠j (sym e)) (j ≡ᵢ? i)) refl ∙ A.∘-zero-l

      πΣδπ : ∀ i → ip.π i A.∘ split ≡ ip.π i
      πΣδπ i =
        ip.π i A.∘ ∑ₕ I (λ i → ip.tuple λ j → δ i j A.∘ ip.π i) ≡⟨ ap (ip.π i A.∘_) (sym (tuple-sum {I} _)) ⟩
        ip.π i A.∘ ip.tuple (λ i → ∑ₕ I λ j → δ j i A.∘ ip.π j) ≡⟨ ip.commute ⟩
        ∑ₕ I (λ j → δ j i A.∘ ip.π j)                           ≡⟨ sum-δ-π i ⟩
        ip.π i                                                  ∎
```

We can now use this `split`{.Agda} morphism to construct the coproduct
structure on $\prod F$. First, the i-th coprojection $\iota_i : F_i \to
\prod F$ is a tuple where all but the $i$-th coordinate are $0$, and $i$
is one.  That is: it's the tuple over $j$ of $\delta_{i,j}$!

```agda
  open Indexed-coproduct
  open is-indexed-coproduct
  coprod : Indexed-coproduct C F
  coprod .ΣF = ip.ΠF
  coprod .ι i = ip.tuple (δ i)
```

We now need to define the "match" function: Given a family $f : F_i \to
Y$, how do we extend this to a (unique) map $m_f$ satisfying $m_f
\iota_j = f_j$? Well, one potential approach is define $m_f$ to be some
kind of sum --- let's say it's a sum over $f'_i$, where $f'_i$ is
something we'll define later. We can still calculate

$$
m_f \iota_j
= (\sum_i f'_i) \iota_{j}
= \sum_i f'_i \iota_j
$$

so we have to choose $f'_i$ such that $f'_i$ is $f$ when $i = j$, and
$0$ otherwise, so only the $f$ term contributes to the above sum. And we
know that, composed with $\iota_j$, the $j$-th projection is the
identity function, and all others are $0$ --- so if we define $f'_i =
f\pi_i$, then we certainly have $(\sum_i f'_i) \iota_j$ = $f$!

```agda
  coprod .has-is-ic = ico where
    m : ∀ {Y} → (∀ i → A.Hom (F i) Y) → A.Hom (ip .Indexed-product.ΠF) Y
    m f = ∑ₕ I λ j → f j A.∘ ip.π j

    ico : is-indexed-coproduct C F _
    ico .match f = m f
    ico .commute {i = i} {f = f} =
      m f A.∘ ip.tuple (δ i)                           ≡⟨ ∑-∘-right {I} _ ⟩
      ∑ₕ I (λ j → (f j A.∘ ip.π j) A.∘ ip.tuple (δ i)) ≡⟨ remark ⟩
      f i                                              ∎
```

<!--
```agda
      where
        remark = ∑-diagonal-lemma (Abelian→Group-on (A.Abelian-group-on-hom _ _)) {I} i
          (λ j → (f j A.∘ ip.π j) A.∘ ip.tuple (λ v → δ i v))
          (A.cancelr ip.commute)
          λ j i≠j → A.pullr (ip.commute ∙ δᵢⱼ i j i≠j (i ≡ᵢ? j))
                  ∙ A.∘-zero-r
```
-->

And how do we show uniqueness? Using our remark about the `split`{.Agda}
morphism defined above! It shows that _any_ map $m' : \prod F \to Y$ has
to factor through something that looks a lot like our definition of $m_f$
above, and if it also satisfies $h\iota_j = f_j$, then a bit of
massaging shows it is _exactly_ $m_f$.

```agda
    ico .unique {h = h} f prf =
      h                                                    ≡⟨ A.intror (sym split-remark) ⟩
      h A.∘ split                                          ≡⟨ ∑-∘-left {I} _ ⟩
      ∑ₕ I (λ i → h A.∘ ip.tuple (λ j → δ i j A.∘ ip.π i)) ≡⟨ ∑-path {I} _ (λ i → ap (h A.∘_) (sym (tuple∘ C F ip _))) ⟩
      ∑ₕ I (λ i → h A.∘ ip.tuple (λ j → δ i j) A.∘ ip.π i) ≡⟨ ∑-path {I} _ (λ i → A.pulll (prf i)) ⟩
      ∑ₕ I (λ i → f i A.∘ ip.π i)                          ≡⟨⟩
      m f                                                  ∎
```
