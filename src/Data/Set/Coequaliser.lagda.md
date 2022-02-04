```agda
open import 1Lab.Prelude

module Data.Set.Coequaliser where
```

<!--
```agda
private variable
  ℓ ℓ' : Level
  A B A' B' A'' B'' : Type ℓ
```
-->

# Set Coequalisers

In their most general form, colimits can be pictured as taking disjoint
unions and then "gluing together" some parts. The "gluing together" part
of that definition is where **coequalisers** come in: If you have
parallel maps $f, g : A \to B$, then the coequaliser $\mathrm{coeq}(f,g)$
can be thought of as "$B$, with the images of $f$ and $g$ identified".

```agda
data coeq (f g : A → B) : Type (level-of A ⊔ level-of B) where
  inc    : B → coeq f g
  glue   : ∀ x → inc (f x) ≡ inc (g x)
  squash : isSet (coeq f g)
```

The universal property of coequalisers, being a type of colimit, is a
_mapping-out_ property: Maps _from_ $\mathrm{coeq}(f,g)$ are maps out of
$B$, satisfying a certain property. Specifically, for a map $h : B \to
C$, if we have $h \circ f = h \circ g$, then the map $f$ factors
(uniquely) through `inc`{.Agda}. The situation can be summarised with
the diagram below.

~~~{.quiver}
\[\begin{tikzcd}
  A & B & {\mathrm{coeq}(f,g)} \\
  && C
  \arrow["f", shift left=1, from=1-1, to=1-2]
  \arrow["g"', shift right=1, from=1-1, to=1-2]
  \arrow["{\mathrm{inc}}", from=1-2, to=1-3]
  \arrow["h"', from=1-2, to=2-3]
  \arrow["{\exists!}", dashed, from=1-3, to=2-3]
\end{tikzcd}\]
~~~

We refer to this unique factoring as `Coeq-rec`{.Agda}.

```
Coeq-rec : ∀ {ℓ} {C : Type ℓ} {f g : A → B} 
      → isSet C → (h : B → C)
      → (∀ x → h (f x) ≡ h (g x)) → coeq f g → C
Coeq-rec cset h h-coeqs (inc x) = h x
Coeq-rec cset h h-coeqs (glue x i) = h-coeqs x i
Coeq-rec cset h h-coeqs (squash x y p q i j) = 
  cset (g x) (g y) (λ i → g (p i)) (λ i → g (q i)) i j
  where g = Coeq-rec cset h h-coeqs
```

An alternative phrasing of the desired universal property is
precomposition with `inc`{.Agda} induces an equivalence between the
"space of maps $B \to C$ which coequalise $f$ and $g$" and the maps
$\mathrm{coeq}(f,g) \to C$. In this sense, `inc`{.Agda} is the universal
map which coequalises $f$ and $g$.

<!--
This is hella confusing, because we need coeq-elimProp to define
`Coeq-univ`, but `Coeq-univ` comes first in the "didactic order"!
-->

<div style="display: flex; flex-flow: column-reverse nowrap;">
<div>

To construct the map above, we used `Coeq-elimProp`{.Agda}, which has
not yet been defined. It says that, to define a dependent function from
`Coeq`{.Agda} to a family of propositions, it suffices to define how it
acts on `inc`{.Agda}: The path constructions don't matter.

```agda
Coeq-elimProp : ∀ {ℓ} {f g : A → B} {C : coeq f g → Type ℓ}
              → (∀ x → isProp (C x))
              → (∀ x → C (inc x))
              → ∀ x → C x
Coeq-elimProp cprop cinc (inc x) = cinc x
```

Since C was assumed to be a family of propositions, we automatically get
the necessary coherences for `glue`{.Agda} and `squash`{.Agda}.

```agda
Coeq-elimProp {f = f} {g = g} cprop cinc (glue x i) = 
  isProp→PathP (λ i → cprop (glue x i)) (cinc (f x)) (cinc (g x)) i
Coeq-elimProp cprop cinc (squash x y p q i j) = 
  isProp→SquareP (λ i j → cprop (squash x y p q i j)) 
    (λ i → g x) (λ i → g (p i)) (λ i → g (q i)) (λ i → g y) i j
  where g = Coeq-elimProp cprop cinc
```

</div>

<div>

Since "the space of maps $h : B \to C$ which coequalise $f$ and $g$" is
a bit of a mouthful, we introduce an abbreviation: Since a colimit is
defined to be a certain universal (co)cone, we call these
`Coeq-cone`{.Agda}s.

```agda
private
  coeq-cone : ∀ {ℓ} (f g : A → B) → Type ℓ → Type _
  coeq-cone {B = B} f g C = Σ[ h ∈ (B → C) ] (h ∘ f ≡ h ∘ g)
```

The universal property of `Coeq`{.Agda} then says that
`Coeq-cone`{.Agda} is equivalent to the maps $\mathrm{coeq}(f,g) \to C$,
and this equivalence is given by `inc`{.Agda}, the "universal
Coequalising map".

```agda
Coeq-univ : ∀ {ℓ} {C : Type ℓ} {f g : A → B}
          → isSet C
          → isEquiv {A = coeq f g → C} {B = coeq-cone f g C} 
            (λ h → h ∘ inc , λ i z → h (glue z i))
Coeq-univ {C = C} {f = f} {g = g} cset = 
  isIso→isEquiv (iso cr' (λ x → refl) islinv) 
  where
    open isIso
    cr' : coeq-cone f g C → coeq f g → C
    cr' (f , f-coeqs) = Coeq-rec cset f (happly f-coeqs)

    islinv : isLeftInverse cr' (λ h → h ∘ inc , λ i z → h (glue z i))
    islinv f = funext (Coeq-elimProp (λ x → cset _ _) λ x → refl)
```

</div>
</div>

# Elimination

Above, we defined what it means to define a dependent function $(x :
\mathrm{coeq}(f,g)) \to C\ x$ when $C$ is a family of propositions, and
what it means to define a non-dependent function $\mathrm{coeq}(f,g) \to
C$. Now, we combine the two notions, and allow dependent elimination
into families of sets:

```agda
Coeq-elim : ∀ {ℓ} {f g : A → B} {C : coeq f g → Type ℓ}
          → (∀ x → isSet (C x))
          → (ci : ∀ x → C (inc x))
          → (∀ x → PathP (λ i → C (glue x i)) (ci (f x)) (ci (g x)))
          → ∀ x → C x
Coeq-elim cset ci cg (inc x) = ci x
Coeq-elim cset ci cg (glue x i) = cg x i
Coeq-elim cset ci cg (squash x y p q i j) = 
  isSet→SquareP (λ i j → cset (squash x y p q i j)) 
    (λ i → g x) (λ i → g (p i)) (λ i → g (q i)) (λ i → g y) i j
  where g = Coeq-elim cset ci cg
```

There is a barrage of combined eliminators, whose definitions are not
very enlightening --- you can mouse over these links to see their types:
`Coeq-elimProp₂`{.Agda} `Coeq-elimProp₃`{.Agda} `Coeq-elim₂`{.Agda}
`Coeq-rec₂`{.Agda}.

<!--
```agda
Coeq-elimProp₂ : ∀ {ℓ} {f g : A → B} {f' g' : A' → B'} 
                  {C : coeq f g → coeq f' g' → Type ℓ}
               → (∀ x y → isProp (C x y))
               → (∀ x y → C (inc x) (inc y))
               → ∀ x y → C x y
Coeq-elimProp₂ cprop f = 
  Coeq-elimProp (λ x → isHLevelΠ 1 λ _ → cprop _ _) 
    λ x → Coeq-elimProp (λ y → cprop _ _) (f x)

Coeq-elimProp₃ : ∀ {ℓ} {f g : A → B} {f' g' : A' → B'} {f'' g'' : A'' → B''}
                   {C : coeq f g → coeq f' g' → coeq f'' g'' → Type ℓ}
               → (∀ x y z → isProp (C x y z))
               → (∀ x y z → C (inc x) (inc y) (inc z))
               → ∀ x y z → C x y z
Coeq-elimProp₃ cprop f = 
  Coeq-elimProp₂ (λ x y → isHLevelΠ 1 λ _ → cprop _ _ _) 
    λ x y → Coeq-elimProp (λ y → cprop _ _ _) (f x y)

Coeq-elim₂ : ∀ {ℓ} {f g : A → B} {f' g' : A' → B'} 
           → {C : coeq f g → coeq f' g' → Type ℓ}
           → (∀ x y → isSet (C x y))
           → (ci : ∀ x y → C (inc x) (inc y))
           → (∀ a x → PathP (λ i → C (glue x i) (inc a)) (ci (f x) a) (ci (g x) a))
           → (∀ a x → PathP (λ i → C (inc a) (glue x i)) (ci a (f' x)) (ci a (g' x)))
           → ∀ x y → C x y
Coeq-elim₂ {f = f} {g = g} {C = C} cset ci r-r l-r =
  Coeq-elim (λ x → isHLevelΠ 2 λ _ → cset _ _) 
    (λ x → Coeq-elim (λ _ → cset _ _) (ci x) (l-r x)) 
    λ x → funextDep λ {x₀} {x₁} → 
      Coeq-elimProp₂ 
        {C = λ x₀ x₁ → (p : x₀ ≡ x₁) 
           → PathP (λ i → C (glue x i) (p i)) 
                   (Coeq-elim (cset _) _ _ x₀) 
                   (Coeq-elim (cset _) _ _ x₁) } 

        (λ _ _ → isHLevelΠ 1 λ _ → isHLevelPathP' 1 (cset _ _) _ _) 

        (λ x₀ _ p → 
          J (λ y p → PathP (λ i → C (glue x i) (p i)) 
                      (Coeq-elim (cset _) (ci (f x)) (l-r (f x)) (inc x₀)) 
                      (Coeq-elim (cset _) (ci (g x)) (l-r (g x)) y)) 
            (r-r x₀ x) p) 
        x₀ x₁

Coeq-rec₂ : ∀ {ℓ} {f g : A → B} {f' g' : A' → B'} {C : Type ℓ}
          → isSet C
          → (ci : B → B' → C)
          → (∀ a x → ci (f x) a ≡ ci (g x) a)
          → (∀ a x → ci a (f' x) ≡ ci a (g' x))
          → coeq f g → coeq f' g' → C
Coeq-rec₂ cset = Coeq-elim₂ (λ _ _ → cset)
```
-->

# Quotients

With dependent sums, we can recover quotients as a special case of
coequalisers. Observe that, by taking the total space of a relation $R :
A \to A \to \ty$, we obtain two projection maps which have as image all
of the possible related elements in $A$. By coequalising these
projections, we obtain a space where any related objects are identified:
The **quotient** $A/R$.

```agda
private
  tot : ∀ {ℓ} → (A → A → Type ℓ) → Type (level-of A ⊔ ℓ)
  tot {A = A} R = Σ[ x ∈ A ] Σ[ y ∈ A ] R x y 

  p1 : ∀ {ℓ} {R : A → A → Type ℓ} → tot R → A
  p1 (x , _ , _) = x

  p2 : ∀ {ℓ} {R : A → A → Type ℓ} → tot R → A
  p2 (_ , x , _) = x
```
<!--
```agda
  variable 
    R S T : A → A → Type ℓ
```
-->

We form the quotient as the aforementioned coequaliser of the two
projections from the total space of $R$:

```agda
_/_ : ∀ {ℓ ℓ'} (A : Type ℓ) (R : A → A → Type ℓ') → Type _
A / R = coeq (p1 {R = R}) p2

quot : ∀ {ℓ ℓ'} {A : Type ℓ} {R : A → A → Type ℓ'} (x y : A) → R x y 
     → Path (A / R) (inc x) (inc y)
quot x y r = glue (x , y , r)
```

Using `Coeq-elim`{.Agda}, we can recover the elimination principle for
quotients:

```
Quot-elim : ∀ {ℓ} {B : A / R → Type ℓ}
          → (∀ x → isSet (B x))
          → (f : ∀ x → B (inc x))
          → (∀ x y (r : R x y) → PathP (λ i → B (quot x y r i)) (f x) (f y))
          → ∀ x → B x
Quot-elim bset f r = Coeq-elim bset f λ { (x , y , w) → r x y w }
```

## Effectivity

The most well-behaved case of quotients is when $R : A \to A \to \ty$
takes values in propositions, is reflexive, transitive and symmetric (an
equivalence relation). In this case, we have that the quotient $A / R$
is **effective**: The map `quot`{.Agda} is an equivalence.

```agda
module _ {A : Type ℓ} {R : A → A → Type ℓ'}
         (Rp : ∀ x y → isProp (R x y))
         (rr : ∀ {x} → R x x)
         (rt : ∀ {x y z} → R x y → R y z → R x z)
         (rs : ∀ {x y} → R x y → R y x)
  where
```

We will show this using an encode-decode method. For each $x : A$, we
define a type family $\mathrm{Code}_x(p)$, which represents an equality
$\mathrm{inc}(x) = y$. Importantly, the fibre over $\mathrm{inc}(y)$
will be $R(x, y)$, so that the existence of functions converting between
$\mathrm{Code}_x(y)$ and paths $\mathrm{inc}(x) = y$ is enough to
establish effectivity of the quotient.

```agda
  private
    Code : A → A / R → Prop ℓ'
    Code x = Quot-elim 
      (λ x → isHLevel-nType 1) 
      (λ y → {- 1 -} R x y , Rp x y)
      λ y z r → 
        Σ≡Prop (λ _ → isProp-isProp) 
          (ua {- 2 -} (propExt (Rp _ _) (Rp _ _) (λ z → rt z r) λ z → rt z (rs r)))
```

We do quotient induction into the `type of propositions`{.Agda
ident=Prop}, which by univalence `is a set`{.Agda ident=isHLevel-nType}.
Since the fibre over $\mathrm{inc}(y)$ must be $R(x, y)$, that's what we
give for the `inc`{.Agda} constructor (`{- 1 -}`{.Agda}, above). For
this to respect the quotient, it suffices to show that, given $R(y,z)$,
we have $R(x,y) \Leftrightarrow R(x,z)$, which follows from the
assumption that $R$ is an equivalence relation (`{- 2 -}`{.Agda}).

```agda
    encode : ∀ x y (p : inc x ≡ y) → Code x y .fst
    encode x y p = subst (λ y → Code x y .fst) p rr

    decode : ∀ x y (p : Code x y .fst) → inc x ≡ y
    decode x y p = 
      Coeq-elimProp {C = λ y → (p : Code x y .fst) → inc x ≡ y} 
        (λ _ → isHLevelΠ 1 λ _ → squash _ _) (λ y r → quot _ _ r) y p
```

For `encode`{.Agda}, it suffices to transport the proof that $R$ is
reflexive along the given proof, and for decoding, we eliminate from the
quotient to a proposition. It boils down to establishing that $R(x,y)
\to \mathrm{inc}(x) \equiv \mathrm{inc}(y)$, which is what the
constructor `quot`{.Agda} says. Putting this all together, we get a
proof that equivalence relations are `effective`{.Agda}.

```agda
  effective : ∀ {x y : A} → isEquiv (quot {R = R} x y)
  effective {x = x} {y} = 
    propExt (Rp x y) (squash _ _) (decode x (inc y)) (encode x (inc y)) .snd 
```

<!--
```agda
Quot-op₂ : ∀ {C : Type ℓ} {T : C → C → Type ℓ'} 
         → (∀ x → R x x) → (∀ y → S y y)
         → (_⋆_ : A → B → C)
         → ((a b : A) (x y : B) → R a b → S x y → T (a ⋆ x) (b ⋆ y))
         → A / R → B / S → C / T
Quot-op₂ Rr Sr op resp = 
  Coeq-rec₂ squash (λ x y → inc (op x y)) 
    (λ { z (x , y , r) → quot _ _ (resp x y z z r (Sr z)) }) 
    λ { z (x , y , r) → quot _ _ (resp z z x y (Rr z) r) }
```
-->