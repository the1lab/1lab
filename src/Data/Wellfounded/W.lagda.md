<!--
```agda
open import 1Lab.Prelude

open import Data.Wellfounded.Properties
open import Data.Wellfounded.Base
```
-->

```agda
module Data.Wellfounded.W where
```

# W-types

The idea behind $W$ types is much simpler than they might appear at
first brush, especially because their form is like that one of the "big
two" $\Pi$ and $\Sigma$. However, the humble $W$ is much simpler: A
value of $W_A B$ is a tree with nodes labelled by $x : A$, and such that
the branching factor of such a node is given by $B(x)$. $W$-types can be
defined inductively:

```agda
data W {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') : Type (ℓ ⊔ ℓ') where
  sup : (x : A) (f : B x → W A B) → W A B
```

<!--
```agda
W-elim : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {C : W A B → Type ℓ''}
       → ({a : A} {f : B a → W A B} → (∀ ba → C (f ba)) → C (sup a f))
       → (w : W A B) → C w
W-elim {C = C} ps (sup a f) = ps (λ ba → W-elim {C = C} ps (f ba))
```
-->

The constructor `sup`{.Agda} stands for **supremum**: it bunches up
(takes the supremum of) a bunch of subtrees, each subtree being given by
a value $y : B(x)$ of the branching factor for that node. The natural
question to ask, then, is: "supremum in _what_ order?". The order given
by the "is a subtree of" relation!

```agda
module _ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} where
  _<_ : W A B → W A B → Type _
  x < sup i f = ∃[ j ∈ B i ] (f j ≡ x)
```

This order is actually well-founded: if we want to prove a property of
$x : W_A B$, we may as well assume it's been proven for any (transitive)
subtree of $x$.

```agda
  W-well-founded : Wf _<_
  W-well-founded (sup x f) = acc λ y y<sup →
    ∥-∥-rec (Acc-is-prop _)
      (λ { (j , p) → subst (Acc _<_) p (W-well-founded (f j)) })
      y<sup
```

## Inductive types are initial algebras

<!--
```agda
module _ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') where
```
-->

We can use $W$ types to illustrate the general fact that inductive types
correspond to *initial algebras* for certain endofunctors. Here, we are working
in the "ambient" $\io$-category of types and functions, and we are interested in the
[polynomial functor] `P`{.Agda}:

[polynomial functor]: Cat.Instances.Poly.html

```agda
  P : Type (ℓ ⊔ ℓ') → Type (ℓ ⊔ ℓ')
  P C = Σ A λ a → B a → C

  P₁ : {C D : Type (ℓ ⊔ ℓ')} → (C → D) → P C → P D
  P₁ f (a , h) = a , f ∘ h
```

A $P$-**algebra** (or $W$-**algebra**) is simply a type $C$ with a function $P\,C \to C$.

```agda
  WAlg : Type _
  WAlg = Σ (Type (ℓ ⊔ ℓ')) λ C → P C → C
```

Algebras form a [category], where an **algebra homomorphism** is a function that respects
the algebra structure.

[category]: Cat.Base.html

```agda
  _W→_ : WAlg → WAlg → Type _
  (C , c) W→ (D , d) = Σ (C → D) λ f → f ∘ c ≡ d ∘ P₁ f
```

Now the inductive `W`{.Agda} type defined above gives us a canonical $W$-algebra:

```agda
  W-algebra : WAlg
  W-algebra .fst = W A B
  W-algebra .snd (a , f) = sup a f
```

The claim is that this algebra is special in that it satisfies a *universal property*:
it is [initial] in the aforementioned category of $W$-algebras.
This means that, for any other $W$-algebra $C$, there is exactly one homomorphism $I \to C$.

[initial]: Cat.Diagram.Initial.html

```agda
  is-initial-WAlg : WAlg → Type _
  is-initial-WAlg I = (C : WAlg) → is-contr (I W→ C)
```

Existence is easy: the algebra $C$ gives us exactly the data we need to specify a function `W A B → C`
by recursion, and the computation rules ensure that this respects the algebra structure definitionally.

```agda
  W-initial : is-initial-WAlg W-algebra
  W-initial (C , c) .centre = W-elim (λ {a} f → c (a , f)) , refl
```

For uniqueness, we proceed by induction, using the fact that `g` is a homomorphism.

```agda
  W-initial (C , c) .paths (g , hom) = Σ-pathp unique coherent where
    unique : W-elim (λ {a} f → c (a , f)) ≡ g
    unique = funext (W-elim λ {a} {f} rec → ap (λ x → c (a , x)) (funext rec)
                                          ∙ sym (hom $ₚ (a , f)))
```

There is one subtlety: being an algebra homomorphism is *not* a [proposition] in general,
so we must also show that `unique`{.Agda} is in fact an **algebra 2-cell**, i.e. that it
makes the following two identity proofs equal:

[proposition]: 1Lab.HLevel.html#is-prop

~~~{.quiver .tall-15}
\[\begin{tikzcd}
	{P\,W} && {P\,C} & {P\,W} && {P\,C} \\
	\\
	W && C & W && C
	\arrow["{\text{sup}}"', from=1-1, to=3-1]
	\arrow["c", from=1-3, to=3-3]
	\arrow[""{name=0, anchor=center, inner sep=0}, "f"', curve={height=12pt}, from=3-1, to=3-3]
	\arrow[""{name=1, anchor=center, inner sep=0}, "{P\,f}"', curve={height=12pt}, from=1-1, to=1-3]
	\arrow[""{name=2, anchor=center, inner sep=0}, "{P\,g}", curve={height=-12pt}, from=1-1, to=1-3]
	\arrow["{\text{sup}}"', from=1-4, to=3-4]
	\arrow["c", from=1-6, to=3-6]
	\arrow[""{name=3, anchor=center, inner sep=0}, "f"', curve={height=12pt}, from=3-4, to=3-6]
	\arrow[""{name=4, anchor=center, inner sep=0}, "g", curve={height=-12pt}, from=3-4, to=3-6]
	\arrow[""{name=5, anchor=center, inner sep=0}, "{P\,g}", curve={height=-12pt}, from=1-4, to=1-6]
	\arrow["{P\,\text{unique}}"{description}, draw=none, from=1, to=2]
	\arrow["{\text{refl}}"{description}, draw=none, from=0, to=1]
	\arrow["{\text{unique}}"{description}, draw=none, from=3, to=4]
	\arrow["{\text{hom}}"{description}, draw=none, from=4, to=5]
\end{tikzcd}\]
~~~

Luckily, this is completely straightforward.

```agda
    coherent : Square (λ i → unique i ∘ W-algebra .snd) refl hom (λ i → c ∘ P₁ (unique i))
    coherent = transpose (flip₁ (∙-filler _ _))
```
