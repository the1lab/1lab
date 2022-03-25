```agda
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Coequaliser
open import Cat.Diagram.Pullback
open import Cat.Diagram.Product
open import Cat.Prelude

import Cat.Reasoning

module Cat.Diagram.Congruence {o ℓ} {C : Precategory o ℓ}
  (fc : Finitely-complete C) where
```

# Congruences

The idea of **congruence** is the categorical rephrasing of the idea of
_equivalence relation_. Recall that an equivalence relation on a [set]
is a family of [propositions] $R : A \times A \to \prop$ satisfying
_reflexivity_ ($R(x,x)$​ for all $x$), _transitivity_ ($R(x,y) \land
R(y,z) \to R(x,z)$), and _symmetry_ ($R(x,y) \to R(y,x)$). Knowing that
$\prop$ classifies [embeddings], we can equivalently talk about an
equivalence relation $R$ as being _just some set_, equipped with a [mono]
$m : R \mono A \times A$.

[set]: 1Lab.HLevel.html#is-set
[propositions]: 1Lab.HLevel.html#is-prop
[embeddings]: 1Lab.Equiv.Embedding.html
[mono]: Cat.Morphism.html#monos

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
    domain = equiv→inverse (subtype-classifier .snd) (λ x → R x , rp x) .fst

    m : domain ↣ (∣ A ∣ × ∣ A ∣)
    m = equiv→inverse (subtype-classifier .snd) (λ x → R x , rp x) .snd

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

**Transitivity**. This one's a doozy. Since $\sets$ has finite limits,
we have an object of "composable pairs" of $d$, namely the pullback
under the cospan $R \xto{p_1} X \xot{p_2} R$.

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
(d \times_A d) \rightrightarrows (A \times A)$ --- which take a
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
pullbacks, we go ahead and assume the category is finitely complete.

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
  source-target = A×A.⟨ rel₁ ∘ R×R.p₁ , rel₂ ∘ R×R.p₂ ⟩

  field
    trans-factors : source-target ≡ m ∘ has-trans

record Congruence-on A : Type (o ⊔ ℓ) where
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
calculation, where we use that $\id{id} = \pi_1 \circ \Delta$.

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
    (pulll A×A.π₁∘factor ∙ idl _)
    (pulll (A×A.π₂∘factor ∙ sym A×A.π₁∘factor) ∙ Pb.square ∙ eliml A×A.π₂∘factor)
```

# Effective congruences

A second example in the same vein as the diagonal is, for any morphism
$f : a \to b$, its _kernel pair_, i.e. the pushout of $a \xto{f} b
\xot{f} a$. Calculating in $\sets$, this is the equivalence relation
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
diagramatically, that $f(x) = f(x)$.

```agda
    cg .has-refl = Kp.limiting {p₁' = id} {p₂' = id} refl
    cg .refl-p₁ = ap (_∘ Kp.limiting refl) a×a.π₁∘factor ∙ Kp.p₁∘limiting
    cg .refl-p₂ = ap (_∘ Kp.limiting refl) a×a.π₂∘factor ∙ Kp.p₂∘limiting
```

Symmetry is witnessed by the map $(A \times_B A) \to (A \times_B A)$
which swaps the components. This one's pretty simple.

```agda
    cg .has-sym = Kp.limiting {p₁' = Kp.p₂} {p₂' = Kp.p₁} (sym Kp.square)
    cg .sym-p₁ = ap (_∘ Kp.limiting (sym Kp.square)) a×a.π₁∘factor
               ∙ sym (a×a.π₂∘factor ∙ sym Kp.p₁∘limiting)
    cg .sym-p₂ = ap (_∘ Kp.limiting (sym Kp.square)) a×a.π₂∘factor
               ∙ sym (a×a.π₁∘factor ∙ sym Kp.p₂∘limiting)
```

<details>
<summary>
Understanding the transitivity map is left as an exercise to the reader.
</summary>

```agda
    cg .has-trans =
      Kp.limiting {p₁' = Kp.p₁ ∘ rel.p₁} {p₂' = Kp.p₂ ∘ rel.p₂} (ap (f ∘_) path)
      where abstract
        path : Kp.p₁ ∘ rel.p₁ ≡ Kp.p₂ ∘ rel.p₂
        path =
          Kp.p₁ ∘ rel.p₁                  ≡˘⟨ ap (_∘ rel.p₁) a×a.π₁∘factor ⟩
          (a×a.π₁ ∘ kernel-pair) ∘ rel.p₁ ≡⟨ rel.square ⟩
          (a×a.π₂ ∘ kernel-pair) ∘ rel.p₂ ≡⟨ ap (_∘ rel.p₂) a×a.π₂∘factor ⟩
          Kp.p₂ ∘ rel.p₂                  ∎

    cg .trans-factors = sym (
        kernel-pair ∘ Kp.limiting _
      ≡⟨ a×a.⟨⟩∘ _ ⟩
        a×a.⟨ Kp.p₁ ∘ Kp.limiting _ , Kp.p₂ ∘ Kp.limiting _ ⟩
      ≡⟨ ap₂ a×a.⟨_,_⟩ (Kp.p₁∘limiting ∙ sym (ap₂ _∘_ a×a.π₁∘factor refl))
                         (Kp.p₂∘limiting ∙ sym (ap₂ _∘_ a×a.π₂∘factor refl)) ⟩
        a×a.⟨ (a×a.π₁ ∘ kernel-pair) ∘ rel.p₁ , (a×a.π₂ ∘ kernel-pair) ∘ rel.p₂ ⟩
      ∎)

  Kernel-pair : Congruence-on a
  Kernel-pair .Congruence-on.domain = _
  Kernel-pair .Congruence-on.inclusion = kernel-pair
  Kernel-pair .Congruence-on.has-is-cong = kernel-pair-is-congruence
```

</details>

A congruence given by the kernel pair of some morphism is called
**effective**. We formalise this property in the following way: A
congruence $R \xmono{m} (a \times a)$ is effective if there exists a map
$f : a \to b$, such that $R$ --- the domain of the congruence --- serves
as a pullback of $a \xto{f} b \xot{f} a$.

```agda
record is-effective-congruence {A} (R : Congruence-on A) : Type (o ⊔ ℓ) where
  private module R = Congruence-on R
  field
    {B} : Ob
    the-map : Hom A B
    has-is-pullback : is-pullback C R.rel₁ the-map R.rel₂ the-map
```

The congruence _given by_ the kernel pair of a map $f$ is effective,
since the pullback of $f$ and $f$ _is_ the pullback of $f$ and $f$.
However, that pullback's projections are not definitionally the same as
the relation's projections, so we must adjust it by a couple of paths:

```agda
kernel-pair-is-effective
  : ∀ {a b} {f : Hom a b}
  → is-effective-congruence (Kernel-pair f)
kernel-pair-is-effective {a = a} {b} {f} = eff where
  open is-effective-congruence
  module a×a = Product (fc.products a a)
  module pb = Pullback (fc.pullbacks f f)
  eff : is-effective-congruence _
  eff .B = _
  eff .the-map = f
  eff .has-is-pullback =
    transport
      (λ i → is-pullback C (a×a.π₁∘factor {p1 = pb.p₁} {p2 = pb.p₂} (~ i)) f
                           (a×a.π₂∘factor {p1 = pb.p₁} {p2 = pb.p₂} (~ i)) f)
      (pb.has-is-pb)
```
