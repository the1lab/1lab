<!--
```agda
open import Cat.Diagram.Coequaliser.RegularEpi
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Coequaliser
open import Cat.Diagram.Pullback
open import Cat.Diagram.Product
open import Cat.Prelude hiding (Kernel-pair)

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Congruence {o ℓ} {C : Precategory o ℓ}
  (fc : Finitely-complete C) where
```

# Congruences

The idea of **congruence** is the categorical rephrasing of the idea of
_equivalence relation_. Recall that an equivalence relation on a [[set]]
is a family of [[propositions]] $R : A \times A \to \prop$ satisfying
_reflexivity_ ($R(x,x)$ for all $x$), _transitivity_ ($R(x,y) \land
R(y,z) \to R(x,z)$), and _symmetry_ ($R(x,y) \to R(y,x)$). Knowing that
$\prop$ classifies [[embeddings]], we can equivalently talk about an
equivalence relation $R$ as being _just some set_, equipped with a
[[monomorphism]] $m : R \mono A \times A$.

We must now identify what properties of the mono $m$ identify $R$ as
being the total space of an equivalence relation. Let us work in the
category of sets for the moment. Suppose $R$ is a relation on $A$, and
$m : d \mono A \times A$ is the monomorphism representing it. Let's
identify the properties of $m$ which correspond to the properties of $R$
we're interested in:

```agda
module _
  {ℓ} {A : Set ℓ} {R : ∣ A ∣ × ∣ A ∣ → Type ℓ}
      {rp : ∀ x → is-prop (R x)}
  where private
    domain : Type ℓ
    domain = subtype-classifier.from (λ x → R x , rp x) .fst

    m : domain ↣ (∣ A ∣ × ∣ A ∣)
    m = subtype-classifier.from (λ x → R x , rp x) .snd

    p₁ p₂ : domain → ∣ A ∣
    p₁ = fst ⊙ fst m
    p₂ = snd ⊙ fst m
```

**Reflexivity**. $R$ is reflexive if, and only if, the morphisms $p_1,
p_2 : d \to A$ have a common left inverse $r : A \to d$.

```agda
    R-refl→common-inverse
      : (∀ x → R (x , x))
      → Σ[ rrefl ∈ (∣ A ∣ → domain) ]
          ( (p₁ ⊙ rrefl ≡ (λ x → x))
          × (p₂ ⊙ rrefl ≡ (λ x → x)))
    R-refl→common-inverse ref = (λ x → (x , x) , ref x) , refl , refl

    common-inverse→R-refl
      : (rrefl : ∣ A ∣ → domain)
      → (p₁ ⊙ rrefl ≡ (λ x → x))
      → (p₂ ⊙ rrefl ≡ (λ x → x))
      → ∀ x → R (x , x)
    common-inverse→R-refl inv p q x = subst R (λ i → p i x , q i x) (inv x .snd)
```

**Symmetry**. There is a map $s : d \to d$ which swaps $p_1$ and $p_2$:

```agda
    R-sym→swap
      : (∀ {x y} → R (x , y) → R (y , x))
      → Σ[ s ∈ (domain → domain) ] ((p₁ ⊙ s ≡ p₂) × (p₂ ⊙ s ≡ p₁))
    R-sym→swap sym .fst ((x , y) , p) = (y , x) , sym p
    R-sym→swap sym .snd = refl , refl

    swap→R-sym
      : (s : domain → domain)
      → (p₁ ⊙ s ≡ p₂) → (p₂ ⊙ s ≡ p₁)
      → ∀ {x y} → R (x , y) → R (y , x)
    swap→R-sym s p q {x} {y} rel =
      subst R (Σ-pathp (happly p _) (happly q _)) (s (_ , rel) .snd)
```

**Transitivity**. This one's a doozy. Since $\Sets$ has finite limits,
we have an object of "composable pairs" of $d$, namely the pullback
under the [cospan] $R \xto{p_1} X \xot{p_2} R$.

[cospan]: Cat.Instances.Shape.Cospan.html

~~~{.quiver}
\[\begin{tikzcd}
  {d \times_A d} && d \\
  \\
  d && A
  \arrow["{q_1}"', from=1-1, to=3-1]
  \arrow["{q_2}", from=1-1, to=1-3]
  \arrow["{p_2}", from=1-3, to=3-3]
  \arrow["{p_1}"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

Transitivity, then, means that the two projection maps $p_1q_1, p_2q_2 :
(d \times_A d) \tto (A \times A)$ --- which take a
"composable pair" to the "first map's source" and "second map's target",
respectively --- factor _through_ $R$, somehow, i.e. we have a $t : (d
\times_A d) \to d$ fitting in the diagram below

~~~{.quiver}
\[\begin{tikzcd}
  && d \\
  {d \times_Ad} && {A \times A}
  \arrow["t", from=2-1, to=1-3]
  \arrow["m", hook, from=1-3, to=2-3]
  \arrow["{(p_1q_1,p_2q_2)}"', from=2-1, to=2-3]
\end{tikzcd}\]
~~~

```agda
    s-t-factor→R-transitive
      : (t : (Σ[ m1 ∈ domain ] Σ[ m2 ∈ domain ] (m1 .fst .snd ≡ m2 .fst .fst))
           → domain)
      → ( λ { (((x , _) , _) , ((_ , y) , _) , _) → x , y } ) ≡ m .fst ⊙ t
      --  ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
      --      this atrocity is "(p₁q₁,p₂q₂)" in the diagram
      → ∀ {x y z} → R (x , y) → R (y , z) → R (x , z)
    s-t-factor→R-transitive compose preserves s t =
      subst R (sym (happly preserves _)) (composite .snd)
      where composite = compose ((_ , s) , (_ , t) , refl)
```

## Generally

Above, we have calculated the properties of a monomorphism $m : R \mono
A \times A$ which identify $R$ as an equivalence relation on the object
$A$. Note that, since the definition relies on both products and
pullbacks, we go ahead and assume the category is [[finitely complete]].

<!--
```agda
open Cat.Reasoning C
open Pullback
open Product
private module fc = Finitely-complete fc

private
  _⊗_ : Ob → Ob → Ob
  A ⊗ B = fc.products A B .apex
```
-->

```agda
record is-congruence {A R} (m : Hom R (A ⊗ A)) : Type (o ⊔ ℓ) where
  no-eta-equality
```

Here's the data of a congruence. Get ready, because there's a lot of it:

<!--
```agda
  private module A×A = Product (fc.products A A)
  rel₁ : Hom R A
  rel₁ = A×A.π₁ ∘ m
  rel₂ : Hom R A
  rel₂ = A×A.π₂ ∘ m
  private module R×R = Pullback (fc.pullbacks rel₁ rel₂)
  private module A×A×A = Pullback (fc.pullbacks rel₁ rel₂)
```
-->

```agda
  field
    has-is-monic : is-monic m
    -- Reflexivity:

    has-refl : Hom A R
    refl-p₁ : rel₁ ∘ has-refl ≡ id
    refl-p₂ : rel₂ ∘ has-refl ≡ id

    -- Symmetry:
    has-sym : Hom R R
    sym-p₁ : rel₁ ∘ has-sym ≡ rel₂
    sym-p₂ : rel₂ ∘ has-sym ≡ rel₁

    -- Transitivity
    has-trans : Hom R×R.apex R

  source-target : Hom R×R.apex A×A.apex
  source-target = A×A.⟨ rel₁ ∘ R×R.p₂ , rel₂ ∘ R×R.p₁ ⟩

  field
    trans-factors : source-target ≡ m ∘ has-trans
```

<!--
```agda
  trans-p₁ : rel₁ ∘ has-trans ≡ rel₁ ∘ A×A×A.p₂
  trans-p₁ =
    pullr (sym trans-factors)
    ∙ A×A.π₁∘factor

  trans-p₂ : rel₂ ∘ has-trans ≡ rel₂ ∘ A×A×A.p₁
  trans-p₂ =
    pullr (sym trans-factors)
    ∙ A×A.π₂∘factor

  unpair-trans
    : ∀ {X} {p₁' p₂' : Hom X R}
    → (sq : rel₁ ∘ p₁' ≡ rel₂ ∘ p₂')
    → m ∘ has-trans ∘ R×R.universal sq ≡ A×A.⟨ rel₁ ∘ p₂' , rel₂ ∘ p₁' ⟩
  unpair-trans sq =
    pulll (sym trans-factors)
    ·· A×A.⟨⟩∘ _
    ·· ap₂ A×A.⟨_,_⟩ (pullr R×R.p₂∘universal) (pullr R×R.p₁∘universal)
```
-->

```agda
record Congruence-on A : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    {domain}    : Ob
    inclusion   : Hom domain (A ⊗ A)
    has-is-cong : is-congruence inclusion
  open is-congruence has-is-cong public
```

# The diagonal

The first example of a congruence we will see is the "diagonal" morphism
$\Delta : A \to (A \times A)$, corresponding to the "trivial relation".

```agda
diagonal : ∀ {A} → Hom A (A ⊗ A)
diagonal {A} = fc.products A A .⟨_,_⟩ id id
```

That the diagonal morphism is monic follows from the following
calculation, where we use that $\id = \pi_1 \circ \Delta$.

```agda
diagonal-is-monic : ∀ {A} → is-monic (diagonal {A})
diagonal-is-monic {A} g h p =
  g                       ≡⟨ introl A×A.π₁∘factor ⟩
  (A×A.π₁ ∘ diagonal) ∘ g ≡⟨ extendr p ⟩
  (A×A.π₁ ∘ diagonal) ∘ h ≡⟨ eliml A×A.π₁∘factor ⟩
  h                       ∎
  where module A×A = Product (fc.products A A)
```

We now calculate that it is a congruence, using the properties of
products and pullbacks. The reflexivity map is given by the identity,
and so is the symmetry map; For the transitivity map, we arbitrarily
pick the first projection from the pullback of "composable pairs"; The
second projection would've worked just as well.

```agda
diagonal-congruence : ∀ {A} → is-congruence diagonal
diagonal-congruence {A} = cong where
  module A×A = Product (fc.products A A)
  module Pb = Pullback (fc.pullbacks (A×A.π₁ ∘ diagonal) (A×A.π₂ ∘ diagonal))
  open is-congruence

  cong : is-congruence _
  cong .has-is-monic = diagonal-is-monic
  cong .has-refl = id
  cong .refl-p₁ = eliml A×A.π₁∘factor
  cong .refl-p₂ = eliml A×A.π₂∘factor
  cong .has-sym = id
  cong .sym-p₁ = eliml A×A.π₁∘factor ∙ sym A×A.π₂∘factor
  cong .sym-p₂ = eliml A×A.π₂∘factor ∙ sym A×A.π₁∘factor
  cong .has-trans = Pb.p₁
  cong .trans-factors = A×A.unique₂
    (A×A.π₁∘factor ∙ eliml A×A.π₁∘factor) (A×A.π₂∘factor ∙ eliml A×A.π₂∘factor)
    (assoc _ _ _ ∙ Pb.square ∙ eliml A×A.π₂∘factor)
    (cancell A×A.π₂∘factor)
```

# Effective congruences

A second example in the same vein as the diagonal is, for any morphism
$f : a \to b$, its _kernel pair_, i.e. the pullback of $a \xto{f} b
\xot{f} a$. Calculating in $\Sets$, this is the equivalence relation
generated by $f(x) = f(y)$ --- it is the subobject of $a \times a$
consisting of those "values which $f$ maps to the same thing".

```agda
module _ {a b} (f : Hom a b) where
  private
    module Kp = Pullback (fc.pullbacks f f)
    module a×a = Product (fc.products a a)

  kernel-pair : Hom Kp.apex a×a.apex
  kernel-pair = a×a.⟨ Kp.p₁ , Kp.p₂ ⟩

  private
    module rel = Pullback
      (fc.pullbacks (a×a.π₁ ∘ kernel-pair) (a×a.π₂ ∘ kernel-pair))

  kernel-pair-is-monic : is-monic kernel-pair
  kernel-pair-is-monic g h p = Kp.unique₂ {p = extendl Kp.square}
    refl refl
    (sym (pulll a×a.π₁∘factor) ∙ ap₂ _∘_ refl (sym p) ∙ pulll a×a.π₁∘factor)
    (sym (pulll a×a.π₂∘factor) ∙ ap₂ _∘_ refl (sym p) ∙ pulll a×a.π₂∘factor)
```

We build the congruence in parts.

```agda
  open is-congruence
  kernel-pair-is-congruence : is-congruence kernel-pair
  kernel-pair-is-congruence = cg where
    cg : is-congruence _
    cg .has-is-monic = kernel-pair-is-monic
```

For the reflexivity map, we take the unique map $f : A \to A \times_B A$
which is characterised by $p_1 f = p_2 f = \mathrm{id}$; This expresses,
diagrammatically, that $f(x) = f(x)$.

```agda
    cg .has-refl = Kp.universal {p₁' = id} {p₂' = id} refl
    cg .refl-p₁ = ap (_∘ Kp.universal refl) a×a.π₁∘factor ∙ Kp.p₁∘universal
    cg .refl-p₂ = ap (_∘ Kp.universal refl) a×a.π₂∘factor ∙ Kp.p₂∘universal
```

Symmetry is witnessed by the map $(A \times_B A) \to (A \times_B A)$
which swaps the components. This one's pretty simple.

```agda
    cg .has-sym = Kp.universal {p₁' = Kp.p₂} {p₂' = Kp.p₁} (sym Kp.square)
    cg .sym-p₁ = ap (_∘ Kp.universal (sym Kp.square)) a×a.π₁∘factor
               ∙ sym (a×a.π₂∘factor ∙ sym Kp.p₁∘universal)
    cg .sym-p₂ = ap (_∘ Kp.universal (sym Kp.square)) a×a.π₂∘factor
               ∙ sym (a×a.π₁∘factor ∙ sym Kp.p₂∘universal)
```

<details>
<summary>
Understanding the transitivity map is left as an exercise to the reader.
</summary>

```agda
    cg .has-trans =
      Kp.universal {p₁' = Kp.p₁ ∘ rel.p₂} {p₂' = Kp.p₂ ∘ rel.p₁} path
      where abstract
        path : f ∘ Kp.p₁ ∘ rel.p₂ ≡ f ∘ Kp.p₂ ∘ rel.p₁
        path =
          f ∘ Kp.p₁ ∘ rel.p₂                  ≡⟨ extendl (Kp.square ∙ ap (f ∘_) (sym a×a.π₂∘factor)) ⟩
          f ∘ (a×a.π₂ ∘ kernel-pair) ∘ rel.p₂ ≡⟨ ap (f ∘_) (sym rel.square) ⟩
          f ∘ (a×a.π₁ ∘ kernel-pair) ∘ rel.p₁ ≡⟨ extendl (ap (f ∘_) a×a.π₁∘factor ∙ Kp.square) ⟩
          f ∘ Kp.p₂ ∘ rel.p₁                  ∎

    cg .trans-factors =
      sym (
        kernel-pair ∘ Kp.universal _
      ≡⟨ a×a.⟨⟩∘ _ ⟩
        a×a.⟨ Kp.p₁ ∘ Kp.universal _ , Kp.p₂ ∘ Kp.universal _ ⟩
      ≡⟨ ap₂ a×a.⟨_,_⟩ (Kp.p₁∘universal ∙ ap₂ _∘_ (sym a×a.π₁∘factor) refl)
                       (Kp.p₂∘universal ∙ ap₂ _∘_ (sym a×a.π₂∘factor) refl) ⟩
        a×a.⟨ (a×a.π₁ ∘ kernel-pair) ∘ rel.p₂ , (a×a.π₂ ∘ kernel-pair) ∘ rel.p₁ ⟩
      ∎)

  Kernel-pair : Congruence-on a
  Kernel-pair .Congruence-on.domain = _
  Kernel-pair .Congruence-on.inclusion = kernel-pair
  Kernel-pair .Congruence-on.has-is-cong = kernel-pair-is-congruence
```

</details>

# Quotient objects

Let $m : R \mono A \times A$ be a congruence on $A$. If $\cC$ has a
coequaliser $q : A \epi A/R$ for the composites $R \mono A \times A \to
A$, then we call $q$ the **quotient map**, and we call $A/R$ the
**quotient** of $R$.

~~~{.quiver .short-2}
\[\begin{tikzcd}
  R & {A \times A} & A & {A/R}
  \arrow["m", hook, from=1-1, to=1-2]
  \arrow[shift left=1, from=1-2, to=1-3]
  \arrow[shift right=1, from=1-2, to=1-3]
  \arrow["q", two heads, from=1-3, to=1-4]
\end{tikzcd}\]
~~~

```agda
is-quotient-of : ∀ {A A/R} (R : Congruence-on A) → Hom A A/R → Type _
is-quotient-of R = is-coequaliser C R.rel₁ R.rel₂
  where module R = Congruence-on R
```

Since $q$ coequalises the two projections, by definition, we have
$q\pi_1m = q\pi_2m$; Calculating in the category of sets where equality
of morphisms is computed pointwise, we can say that "the images of
$R$-related elements under the quotient map $q$ are equal". By
definition, the quotient for a congruence is a [regular epimorphism].

[regular epimorphism]: Cat.Diagram.Coequaliser.RegularEpi.html

```agda
open is-regular-epi

quotient-regular-epi
  : ∀ {A A/R} {R : Congruence-on A} {f : Hom A A/R}
  → is-quotient-of R f → is-regular-epi C f
quotient-regular-epi quot .r = _
quotient-regular-epi quot .arr₁ = _
quotient-regular-epi quot .arr₂ = _
quotient-regular-epi quot .has-is-coeq = quot
```

If $R \hookrightarrow A \times A$ has a quotient $q : A \to A/R$, and
$R$ is additionally the pullback of $q$ along itself, then $R$ is called
an **effective congruence**, and $q$ is an **effective coequaliser**.
Since, as mentioned above, the kernel pair of a morphism is "the
congruence of equal images", this says that an effective quotient
identifies _exactly those_ objects related by $R$, and no more.

```agda
record is-effective-congruence {A} (R : Congruence-on A) : Type (o ⊔ ℓ) where
  private module R = Congruence-on R
  field
    {A/R}          : Ob
    quotient       : Hom A A/R
    has-quotient   : is-quotient-of R quotient
    is-kernel-pair : is-pullback C R.rel₁ quotient R.rel₂ quotient
```

If $f$ is the coequaliser of its kernel pair --- that is, it is an
[effective epimorphism] --- then it is an effective congruence, and
vice-versa.

[effective epimorphism]: Cat.Diagram.Coequaliser.RegularEpi.html

```agda
kernel-pair-is-effective
  : ∀ {a b} {f : Hom a b}
  → is-quotient-of (Kernel-pair f) f
  → is-effective-congruence (Kernel-pair f)
kernel-pair-is-effective {a = a} {b} {f} quot = epi where
  open is-effective-congruence hiding (A/R)
  module a×a = Product (fc.products a a)
  module pb = Pullback (fc.pullbacks f f)

  open is-coequaliser
  epi : is-effective-congruence _
  epi .is-effective-congruence.A/R = b
  epi .quotient = f
  epi .has-quotient = quot
  epi .is-kernel-pair =
    transport
      (λ i → is-pullback C (a×a.π₁∘factor {p1 = pb.p₁} {p2 = pb.p₂} (~ i)) f
                           (a×a.π₂∘factor {p1 = pb.p₁} {p2 = pb.p₂} (~ i)) f)
      pb.has-is-pb

kp-effective-congruence→effective-epi
  : ∀ {a b} {f : Hom a b}
  → (eff : is-effective-congruence (Kernel-pair f))
  → is-effective-epi C (eff .is-effective-congruence.quotient)
kp-effective-congruence→effective-epi {f = f} cong = epi where
  module cong = is-effective-congruence cong
  open is-effective-epi
  epi : is-effective-epi C _
  epi .kernel = Kernel-pair _ .Congruence-on.domain
  epi .p₁ = _
  epi .p₂ = _
  epi .is-kernel-pair = cong.is-kernel-pair
  epi .has-is-coeq = cong.has-quotient
```
