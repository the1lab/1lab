<!--
```agda
open import Cat.Diagram.Coequaliser.RegularEpi
open import Cat.Diagram.Pushout.Properties
open import Cat.Instances.Sets.Cocomplete
open import Cat.Diagram.Coequaliser
open import Cat.Morphism.Strong.Epi
open import Cat.Instances.Functor
open import Cat.Diagram.Pushout
open import Cat.Prelude

open import Homotopy.Connectedness

import Cat.Reasoning as Cr
```
-->

```agda
module Data.Set.Surjection where
```

<!--
```agda
open is-coequaliser
open is-regular-epi
open Coequaliser
open Pushout
```
-->

# Surjections between sets {defines="surjections-between-sets"}

Here we prove that surjective maps are exactly the [regular epimorphisms]
in the category of sets: Really, we prove that surjections are regular
epimorphisms (this is straightforward), then we prove that every
[epimorphism] is a surjection (this takes a detour). Putting these
together, we get _every epimorphism is regular_ as a corollary.

[regular epimorphisms]: Cat.Diagram.Coequaliser.RegularEpi.html#regular-epimorphisms
[epimorphism]: Cat.Morphism.html#epis

## Surjections are epic {defines="surjections-are-epic"}

This is the straightforward direction: We know (since $\Sets$ has
pullbacks) that if a morphism is going to be a regular epimorphism, then
it must be an _effective_ epimorphism, too: so if it is to coequalise
any morphisms, it certainly coequalises its kernel pair.

```agda
surjective→regular-epi
  : ∀ {ℓ} (c d : n-Type ℓ 2) (f : ∣ c ∣ → ∣ d ∣)
  → is-surjective f
  → is-regular-epi (Sets ℓ) {c} {d} f
surjective→regular-epi c _ f x .r = el! (Σ ∣ c ∣ λ x → Σ ∣ c ∣ λ y → f x ≡ f y)
surjective→regular-epi _ _ f x .arr₁ = λ (y , _ , _) → y
surjective→regular-epi _ _ f x .arr₂ = λ (_ , y , _) → y
```

That's our choice of cofork: it remains to show that $f$ coequalises
this. Given any map $e' : c \to F$, element $x : d$, mere fibre
$f^*(x)$, and proof $p$ that $e'$ is constant on the kernel pair of $f$
(i.e. that it also coequalises the kernel pair cofork), we can construct
an element of $F$: since $e'$ is suitably constant, we can use the
elimination principle for $\| f^*x \| \to F$, since $F$ is a set.

```agda
surjective→regular-epi c d f surj .has-is-coeq = coeqs where
  go : ∀ {F} (e' : ∣ c ∣ → ∣ F ∣) p (x : ∣ d ∣) → ∥ fibre f x ∥ → ∣ F ∣
  go e' p x =
    ∥-∥-rec-set! (λ x → e' (x .fst))
      (λ x y → p $ₚ (x .fst , y .fst , x .snd ∙ sym (y .snd)))
```

After a small amount of computation to move the witnesses of
surjectivity out of the way, we get what we wanted.

```agda
  coeqs : is-coequaliser (Sets _) _ _ _
  coeqs .coequal i (x , y , p) = p i
  coeqs .universal {F} {e'} p x = go {F = F} e' p x (surj x)
  coeqs .factors {F} {e'} {p = p} = funext λ x →
    ∥-∥-elim {P = λ e → go {F} e' p (f x) e ≡ e' x}
      (λ x → hlevel 1) (λ e → p $ₚ (e .fst , x , e .snd)) (surj (f x))
  coeqs .unique {F} {e'} {p} {colim} comm = funext λ a →
    ∥-∥-elim {P = λ e → go {F} e' p a e ≡ colim a} (λ x → hlevel 1)
      (λ x → sym comm ·ₚ x .fst ∙ ap colim (x .snd))
      (surj a)
```

<!--
```agda
surjective→strong-epi
  : ∀ {ℓ} (c d : n-Type ℓ 2) (f : ∣ c ∣ → ∣ d ∣)
  → is-surjective f
  → is-strong-epi (Sets ℓ) {c} {d} f
surjective→strong-epi c d f f-surj =
  is-regular-epi→is-strong-epi (Sets _) f $
  surjective→regular-epi c d f f-surj

surjective→epi
  : ∀ {ℓ} (c d : n-Type ℓ 2) (f : ∣ c ∣ → ∣ d ∣)
  → is-surjective f
  → Cr.is-epic (Sets ℓ) {c} {d} f
surjective→epi c d f surj {c = x} =
  is-regular-epi→is-epic (surjective→regular-epi c d f surj) {c = x}
```
-->

# Epis are surjective {defines="epis-are-surjective"}

Now _this_ is the hard direction. Our proof follows [@Rijke:2015, §2.9],
so if the exposition below doesn't make a lot of sense, be sure to check
their paper, too. We define a higher inductive type standing for the
_cofibre_ of $f$, also known as the _mapping cone_. Strictly speaking,
this is the homotopy pushout

~~~{.quiver}
\[\begin{tikzcd}
  A && B \\
  \\
  \top && {\mathrm{Cofibre}(f)\text{,}}
  \arrow["{\mathrm{pt}}"', from=3-1, to=3-3]
  \arrow["{\mathrm{inr}}", from=1-3, to=3-3]
  \arrow["f", from=1-1, to=1-3]
  \arrow["{!}"', from=1-1, to=3-1]
  \arrow["\lrcorner"{anchor=center, pos=0.125, rotate=180}, draw=none, from=3-3, to=1-1]
\end{tikzcd}\]
~~~

but Mikan makes it very convenient to define a purpose-built HIT
in-line. We use the names "tip", "base", and "cone" to evoke the
construction of a cone in solid geometry: the `tip`{.Agda} is.. the tip,
the `base`{.Agda} is the circle, and the `cone`{.Agda} is the triangular
side which we have rotated around the vertical axis.

```agda
data Cofibre {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) : Type (ℓ ⊔ ℓ') where
  tip  : Cofibre f
  base : B → Cofibre f
  cone : ∀ a → tip ≡ base (f a)
```

What's important here is that if a map $f$ has [[connected]] cofibre, then
it is a surjection --- so our proof that epis are surjective will factor
through showing that epis have connected cofibres^[note that all of
these types are propositions, so we have a bunch of equivalences].

```agda
connected-cofibre→surjective
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B)
  → is-connected (Cofibre f)
  → is-surjective f
connected-cofibre→surjective {A = A} {B = B} f conn x = transport cen (lift tt) where
```

We define a family $P$ of propositions over $\rm{Cofibre}(f)$ which maps
`tip`{.Agda} to the unit proposition and the base point with coordinate
$x$ to the fibre $f^x$. Since $\rm{Prop}$ is a set, $P$ extends to a map
$P' : \| \rm{Cofibre}(f) \|_0 \to \rm{Prop}$.

```agda
  P : Cofibre f → Prop _
  P tip      = el! (Lift _ ⊤)
  P (base x) = el! ∥ fibre f x ∥
  P (cone a i) =
    n-ua {X = el! (Lift _ ⊤)} {Y = el! ∥ fibre f (f a) ∥}
      (prop-ext! (λ _ → inc (a , refl)) λ _ → lift tt) i

  P' : ∥ Cofibre f ∥₀ → Prop _
  P' = ∥-∥₀-elim (λ _ → hlevel 2) P
```

Letting $x$ be an element of the codomain, and since by assumption $f$'s
cofibre is connected, we have a path

$$
\top = P'(\rm{tip}) = P'(\rm{base}_x) = \| f^x \|
$$,

so since the unit type is trivially inhabited, so is the fibre of $f$
over $x$: $f$ is surjective.

```agda
  cen : Lift _ ⊤ ≡ ∥ fibre f x ∥
  cen = ap ∣_∣ (ap P' (is-contr→is-prop conn (inc tip) (inc (base x))))
```

## Epis have connected cofibre

Now suppose that $f$ is an epic morphism ^[by which we mean it is an
epimorphism --- it needn't be like the Odyssey] ^[and yes, we did write
"an epic morphism" just to make the joke]. We know that the
set-truncation of $f$'s cofibre is inhabited (since every cofibre is
inhabited), so it remains to show that any two points are merely equal.

```agda
epi→connected-cofibre
  : ∀ {ℓ} (c d : n-Type ℓ 2) (f : ∣ c ∣ → ∣ d ∣)
  → Cr.is-epic (Sets ℓ) {c} {d} f
  → is-connected (Cofibre f)
epi→connected-cofibre c d f epic = contr (inc tip) $
  ∥-∥₀-elim (λ _ → is-prop→is-set (squash _ _)) λ w →
    ∥-∥₀-path.from (hom w)
  where
```

Let $x : d$ --- we'll show that $\| \rm{tip} = \rm{base}_x \|$. Here's
where we use $f$'s epimorphy: we have a homotopy $| \rm{tip} | = |
\rm{base}_{(f x)} |$, namely the `cone`{.Agda} --- and since we can
write its left-hand-side as the composition of $f$ with a constant
function, $f$ gives us a path $| \rm{tip} | = | \rm{base}_x |$ ---
which, by the characterisation of paths in the [[set truncation]], means
we merely have $\| \rm{tip} = \rm{base}_x \|$.

```agda
    go : ∀ x → ∥ tip ≡ base x ∥
    go x = ∥-∥₀-path.to (p $ₚ x) where
      p = epic {c = el ∥ Cofibre f ∥₀ squash}
        (λ _ → inc tip)
        (λ x → inc (base x))
        (funext λ x → ap ∥_∥₀.inc (cone x))
```

An appeal to induction over the cofibre completes the proof:
Epimorphisms have connected cofibres. Note that the path case is
discharged automatically since we're mapping into a proposition.

```agda
    hom : ∀ w → ∥ tip ≡ w ∥
    hom tip = inc refl
    hom (base x) = go x
    hom (cone a i) = is-prop→pathp (λ i → ∥_∥.squash {A = tip ≡ cone a i})
      (inc refl) (go (f a)) i
```

And, composing this with the previous step, we have what we originally
set out to prove: all $\Sets$-epimorphisms are regular, because they're
all surjections!

```agda
epi→surjective
  : ∀ {ℓ} (c d : n-Type ℓ 2) (f : ∣ c ∣ → ∣ d ∣)
  → Cr.is-epic (Sets ℓ) {c} {d} f
  → is-surjective f
epi→surjective {ℓ} c d f epi x =
  connected-cofibre→surjective f (epi→connected-cofibre c d f (λ {x} → epi {x})) x
```
