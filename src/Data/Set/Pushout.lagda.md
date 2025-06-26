<!--
```agda
open import 1Lab.Prelude

open import Data.Set.Coequaliser
open import Data.Sum
```
-->

```agda
module Data.Set.Pushout where
```

# Pushouts of sets

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A B C : Type ℓ
  f g : C → A

pattern incl x = inc (inl x)
pattern incr x = inc (inr x)
```
-->

The [[pushout]] of two [[sets]] can be, as usual, constructed as a
[[coequaliser]] of maps into a [[coproduct]]. However, pushouts in the
category $\Sets$ have a nice property: they preserve [[embeddings]].
This module is dedicated to proving this.

```agda
Pushout
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  → (f : C → A) (g : C → B)
  → Type (ℓ ⊔ ℓ' ⊔ ℓ'')
Pushout {A = A} {B} {C} f g = Coeq {B = A ⊎ B} (λ z → inl (f z)) (λ z → inr (g z))
```

<!--
```agda
swap-pushout : Pushout f g → Pushout g f
swap-pushout (incl x) = incr x
swap-pushout (incr x) = incl x
swap-pushout (glue x i) = glue x (~ i)
swap-pushout (squash x y p q i j) =
  let f = swap-pushout in squash (f x) (f y) (λ i → f (p i)) (λ i → f (q i)) i j

swap-swap : swap-pushout {f = f} {g = g} ∘ swap-pushout ≡ λ x → x
swap-swap = ext λ where
  (inl x) → refl
  (inr x) → refl

swap-pushout-is-equiv : is-equiv (swap-pushout {f = f} {g = g})
swap-pushout-is-equiv = is-iso→is-equiv $
  iso swap-pushout (happly swap-swap) (happly swap-swap)
```
-->

## Pushouts of injections

<!--
```agda
module
  _ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
    ⦃ bset : H-Level B 2 ⦄
    (f : C → A) (g : C → B) (f-emb : is-embedding f)
    where
```
-->

Let us now get to the proof of our key result. Suppose $f : C \mono A$
is an embedding and $g : C \to B$ is some other map. Our objective is to
prove that, in the square

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  C \&\& B \\
  \\
  A \&\& {A \sqcup_C B}
  \arrow["g", from=1-1, to=1-3]
  \arrow["f"', hook, from=1-1, to=3-1]
  \arrow["{\rm{incr}}", from=1-3, to=3-3]
  \arrow["{\rm{incl}}"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

the constructor $\rm{incl} : B \to A \sqcup_C B$ is an embedding.^[In
this situation, the map $\rm{incr}$ is often referred to as the **cobase
change** of $f$ along $g$.]. As usual when working with higher inductive
types, we'll employ encode-decode, characterising the path spaces based
at some $b : B$ by means of a family $F$ over $A \sqcup_C B$. We know
already we want $F(\rm{incr}\, b')$ to be $b = b'$, since this is
exactly injectivity of $\rm{incr}$. But what should the fibre over
$\rm{incl}\, a$ be?

A possibility comes from generalising the generating equality
$\rm{glue}$ from identifying $\rm{incl} (f x) = \rm{incr} (g x)$ to
identifying any $a$, $b$ provided we can cough up $c : C$ with $f c = a$
and $g c = b$. While this is a trivial rephrasing, it does inspire
confidence: can we expect $\rm{incr}\, b = \rm{incl}\, a$ to be given by
fibres of $\langle f, g \rangle$ over $(a, b)$?

Well, if this were the case, these fibres would necessarily need to
be propositions, so we can start by showing that. The proof turns out
very simple: the type $$\sum_{c\, :\, C} (f c = a) \times (g c = b)$$ is
equivalent to $$\sum_{(c,-)\, :\, f^*(a)} g^*(c)$$, and since $f$ is an
embedding, this is a subtype of a proposition.

<!--
```agda
  private module _ (b : B) where
```
-->

```agda
    rem₁ : ∀ a → is-prop (Σ[ c ∈ C ] (f c ≡ a) × (g c ≡ b))
    rem₁ a (c , α , β) (c' , α' , β') = ap fst it ,ₚ ap snd it ,ₚ prop! where
      it = f-emb a (c , α) (c' , α')
```

<!--
```agda
    instance
      rem₁' : ∀ {a n} → H-Level (Σ[ c ∈ C ] (f c ≡ a) × (g c ≡ b)) (suc n)
      rem₁' {a} = prop-instance (rem₁ a)
      {-# OVERLAPPING rem₁' #-}
```
-->

We can then turn back to defining our family $F$. Both of the point
cases are handled, and since we're mapping into $\Omega$, that also
handles the truncation.

```agda
    code : Pushout f g → Prop (ℓ ⊔ ℓ' ⊔ ℓ'')
    code (incr b') = el! (Lift (ℓ ⊔ ℓ'') (b ≡ b'))
    code (incl a)  = el! (Σ[ c ∈ C ] (f c ≡ a) × (g c ≡ b))
```

It remains to handle the paths. Since we're mapping into a universe, it
will suffice to show that the types
$$\sum_{c : C} (f c = f x) \times (g c = b)$$
and $b = g x$ are equivalent, and, since we're mapping into
propositions, it will suffice to provide functions in either direction.
Going backwards, this is trivial; In the other direction, we show $b =
g x$ since $f c = f x$ implies $c = x$ by injectivity of $f$, and
we have $g c = b$ by assumption.

```agda
    code (glue x i) =
      let
        from : Lift _ (b ≡ g x) → Σ[ c ∈ C ] (f c ≡ f x) × (g c ≡ b)
        from (lift p) = x , refl , sym p

        to : Σ[ c ∈ C ] (f c ≡ f x) × (g c ≡ b) → Lift _ (b ≡ g x)
        to (x , α , β) = lift (sym β ∙ ap g (ap fst (f-emb _ (_ , α) (_ , refl))))
```

<!--
```agda
      in n-ua
          {X = el! (Σ[ c ∈ C ] (f c ≡ f x) × (g c ≡ b))}
          {Y = el! (Lift (ℓ ⊔ ℓ'') (b ≡ g x))}
          (prop-ext! to from) i

    code (squash x y p q i j) = n-Type-is-hlevel 1
      (code x) (code y) (λ i → code (p i)) (λ i → code (q i)) i j
```
-->

We then have the two encoding functions. In the case with matched
endpoints, we have exactly our original goal: injectivity of
`incr`{.Agda}.

```agda
  encodeᵣ : injective incr
  encodeᵣ {a} p = transport (λ i → ⌞ code a (p i) ⌟) (lift refl) .lower
```

<!--
```agda
  f-inj→incr-inj : is-embedding {A = B} {B = Pushout f g} incr
  f-inj→incr-inj = injective→is-embedding! encodeᵣ
```
-->

In the mismatched case, we have a function turning paths $\rm{incr}\, b
= \rm{incl}\, a$ into a fibre of $\langle f, g \rangle$ over $(a, b)$.
It's easy to show that projecting the point is the inverse to $g$,
considered as a function $f^*(x) \to \rm{incr}^*(\rm{incl}\, x)$.

```agda
  encodeₗ
    : ∀ {a b} (p : incr b ≡ incl a)
    → Σ[ c ∈ C ] (f c ≡ a × g c ≡ b)
  encodeₗ {b = b} p = transport (λ i → ⌞ code b (p i) ⌟) (lift refl)

  pushout-is-pullback' : ∀ x → fibre f x ≃ fibre {B = Pushout f g} incr (incl x)
  pushout-is-pullback' x .fst (y , p) = g y , sym (glue y) ∙ ap incl p
  pushout-is-pullback' x .snd = is-iso→is-equiv $ iso from ri λ f → f-emb x _ _ where
    from : fibre {B = Pushout f g} incr (incl x) → fibre f x
    from (y , p) with (c , α , β) ← encodeₗ p = c , α

    ri : is-right-inverse from (pushout-is-pullback' x .fst)
    ri (y , p) with (c , α , β) ← encodeₗ p = Σ-prop-path! β
```

Finally, we can extend this to an equivalence between $C$ and the
pullback of $\rm{incl}$ along $\rm{incr}$ by general
[[family-fibration|object classifiers]] considerations.

```agda
  _ : C ≃ (Σ[ a ∈ A ] Σ[ b ∈ B ] incl a ≡ incr b)
  _ = C                                       ≃⟨ Total-equiv f ⟩
      Σ[ a ∈ A ] fibre f a                    ≃⟨ Σ-ap-snd pushout-is-pullback' ⟩
      Σ[ a ∈ A ] fibre incr (incl a)          ≃⟨⟩
      Σ[ a ∈ A ] Σ[ b ∈ B ] (incr b ≡ incl a) ≃⟨ Σ-ap-snd (λ a → Σ-ap-snd λ b → sym-equiv) ⟩
      Σ[ a ∈ A ] Σ[ b ∈ B ] (incl a ≡ incr b) ≃∎
```

<!--
```agda
  -- That equivalence computes like garbage on the third component, and
  -- we can do better:

  pushout-is-pullback : C ≃ (Σ[ a ∈ A ] Σ[ b ∈ B ] incl a ≡ incr b)
  pushout-is-pullback .fst x = f x , g x , glue x
  pushout-is-pullback .snd = is-iso→is-equiv (iso from ri λ x → refl) where
    module _ (x : _) (let β = x .snd .snd) where
      from : C
      from = encodeₗ (sym β) .fst

      ri : (f from , g from , glue from) ≡ (_ , _ , β)
      ri = encodeₗ (sym β) .snd .fst ,ₚ encodeₗ (sym β) .snd .snd ,ₚ prop!

module _ ⦃ aset : H-Level A 2 ⦄ (f : C → A) (g : C → B) (g-emb : is-embedding g) where
  g-inj→incl-inj : is-embedding {A = A} {B = Pushout f g} incl
  g-inj→incl-inj = ∘-is-embedding
    (is-equiv→is-embedding swap-pushout-is-equiv)
    (f-inj→incr-inj g f g-emb)
```
-->
