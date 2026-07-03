<!--
```agda
open import 1Lab.Reflection.Copattern

open import Cat.Diagram.Pullback.Properties
open import Cat.Displayed.GenericObject
open import Cat.Instances.Sets.Complete
open import Cat.Diagram.Pullback.Along
open import Cat.Diagram.Limit.Finite
open import Cat.Displayed.Cartesian
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Instances.Sets
open import Cat.Prelude hiding (Ω ; true)

import Cat.Displayed.Instances.Subobjects.Reasoning as Subr
import Cat.Displayed.Instances.Subobjects as Subobjs
import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Omega where
```

# Subobject classifiers {defines="generic-subobject subobject-classifier"}

In an arbitrary category $\cC$, a [[subobject]] of $X$ is, colloquially
speaking, given by a monomorphism $m : A \mono X$. Formally, though, we
must consider the object $A$ to be part of this data, since we can only
speak of morphisms if we already know their domain and codomain. The
generality in the definition means that the notion of subobject applies
to completely arbitrary $\cC$, but in completely arbitrary situations,
the notion might be _very_ badly behaved.

There are several observations we can make about $\cC$ that "tame" the
behaviour of $\Sub_{\cC}(X)$. For example, if it has [[pullbacks]], then
$\Sub(-)$ is a [[fibration]], so that there is a universal way of
re-indexing a subobject $x : \Sub(X)$ along a morphism $f : Y \to X$,
and if it has [[images]], it's even a [[bifibration]], so that each of
these reindexings has a [[left adjoint]], giving an interpretation of
existential quantifiers. If $\cC$ is a [[regular category]], existential
quantifiers and substitution commute, restricting the behaviour of
subobjects even further.

However, there is one assumption we can make about $\cC$ that rules them
all: it has a **generic subobject**, so that $\Sub(X)$ is equivalent to
a given $\hom$-set in $\cC$. A generic subobject is a morphism $\top :
\Omega* \to \Omega$ so that, for any a subobject $m : A \mono X$, there
is a _unique_ arrow $\name{m}$ making the square

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  A \&\& \Omega* \\
  \\
  X \&\& \Omega
  \arrow["", from=1-1, to=1-3]
  \arrow["\top", from=1-3, to=3-3]
  \arrow["{\name{m}}"', from=3-1, to=3-3]
  \arrow["m"', hook, from=1-1, to=3-1]
\end{tikzcd}\]
~~~

into a pullback. We can investigate this definition by instantiating it
in $\Sets$, which _does_ have a generic subobject. Given an
[[embedding]] $m : A \mono X$, we have a family of propositions
$\name{m} : X \to \Omega$ which maps $x : X$ to $m^*(x)$, the
`fibre`{.Agda} of $m$ over $x$. The square above _also_ computes a
fibre, this time of $\name{m}$, and saying that it is $m$ means that
$\name{m}$ assigns $\top$ to precisely those $x : X$ which are in $m$.

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) where
  open Cat.Reasoning C
  open Subobjs C
```
-->

```agda
  record is-generic-subobject {Ω} (true : Subobject Ω) : Type (o ⊔ ℓ) where
    field
      name : ∀ {X} (m : Subobject X) → Hom X Ω
      classifies
        : ∀ {X} (m : Subobject X)
        → is-pullback-along C (m .map) (name m) (true .map)
      unique
        : ∀ {X} {m : Subobject X} {nm : Hom X Ω}
        → is-pullback-along C (m .map) nm (true .map)
        → nm ≡ name m
```

::: terminology
We follow [@Elephant, A1.6] for our terminology: the morphism $\top : 1
\to \Omega$ is called the **generic subobject**, and $\Omega$ is the
**subobject classifier**. This differs from the terminology in the
[nLab](https://ncatlab.org/nlab/show/subobject+classifier), where the
_morphism_ $\top$ is called the subobject classifier.
:::

```agda
  record Subobject-classifier : Type (o ⊔ ℓ) where
    field
      {Ω}     : Ob
      true    : Subobject Ω
      generic : is-generic-subobject true
    open is-generic-subobject generic public
```

While the definition of `is-generic-subobject`{.Agda} can be stated
without assuming that $\cC$ has any limits at all, we'll need to assume
that $\cC$ has [[pullbacks]] to get anything of value done. Before we
get started, however, we'll prove a helper theorem that serves as a
"smart constructor" for `Subobject-classifier`{.Agda}, simplifying the
verification of the universal property in case $\cC$ is
[[univalent|univalent category]] and has all [[finite limits]] (in
particular, a [[terminal object]]).

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} (fc : Finitely-complete C) (cat : is-category C) where
  open Subobject-classifier
  open is-generic-subobject
  open Cat.Reasoning C
  open Subr (fc .Finitely-complete.pullbacks)
  open Terminal (fc .Finitely-complete.terminal) using (top)

  point→subobject : ∀ {A} (it : Hom top A) → Subobject A
  point→subobject it .dom = top
  point→subobject it .map = it
  point→subobject it .monic g h x = Terminal.!-unique₂ (fc .Finitely-complete.terminal) _ _
```
-->

Assuming that we have a terminal object, we no longer need to specify
the arrow $\true$ as an arbitrary element of $\Sub(\Omega)$ --- we can
instead ask for a *point* $\true : \top \to \Omega$ instead. Since we
have pullbacks, we also have the change-of-base operation $f^*(-) :
\Sub(B) \to \Sub(A)$ for any $f : A \to B$, which allows us to
simplify the condition that "$m$ is the pullback of $n$ `along`{.Agda
ident=is-pullback-along} $f$", which requires constructing a pullback
square, to the simpler $m \cong f^*n$. The theorem is that it suffices
to ask for:

- The point $\true : \top \to \Omega$ corresponding to the generic
  subobject,
- An operation $\name{-} : \Sub(A) \to \hom(A, \Omega)$ which maps
  subobjects to their names,
- A witness that, for any $m : \Sub(A)$, we have
  $m \cong \name{m}^*\true$, and
- A witness that, for any $h : \hom(A, \Omega)$, we have
  $h = \name{h^*\true}$.

These two conditions amount to saying that $\name{-}$ and $(-)^*\top$
form an [[equivalence]] between the sets $\Sub(A)$ and $\hom(A,
\Omega)$, for all $A$. Note that we do not need to assume naturality for
$\name{-}$ since it is an inverse equivalence to $(-)^*\true$, which is
already natural.

```agda
  from-classification
    : ∀ {Ω} (true : Hom top Ω)
    → (name : ∀ {A} (m : Subobject A) → Hom A Ω)
    → (∀ {A} (m : Subobject A) → m ≅ₘ name m ^* point→subobject true)
    → (∀ {A} (h : Hom A Ω) → name (h ^* point→subobject true) ≡ h)
    → Subobject-classifier C
  from-classification tru nm invl invr = done where
    done : Subobject-classifier C
    done .Ω = _
    done .true = point→subobject tru
    done .generic .name = nm
    done .generic .classifies m = iso→is-pullback-along {m = m} {n = point→subobject tru} (invl m)
```

Note that the uniqueness part of the universal property is satisfied by
the last constraint on $\name{-}$: the `is-pullback-along`{.Agda}
assumption amounts to saying that $m \is h'^*\true$, by univalence of
$\Sub(A)$; so we have $$\name{m} = \name{h'^*\true} = h'$$.

```agda
    done .generic .unique {m = m} {h'} p =
      let
        rem₁ : m ≡ h' ^* point→subobject tru
        rem₁ = Sub-is-category cat .to-path $
          is-pullback-along→iso {m = m} {n = point→subobject tru} p
      in sym (ap nm rem₁ ∙ invr _)
```

<!--
```agda
  record make-subobject-classifier : Type (o ⊔ ℓ) where
    field
      {Ω}  : Ob
      true : Hom top Ω
      name : ∀ {A} (m : Subobject A) → Hom A Ω
      named-name : ∀ {A} (m : Subobject A) → m ≅ₘ name m ^* point→subobject true
      name-named : ∀ {A} (h : Hom A Ω) → name (h ^* point→subobject true) ≡ h

module _ where
  open make-subobject-classifier hiding (Ω)

  to-subobject-classifier : ∀ {o ℓ} {C : Precategory o ℓ} (fc : Finitely-complete C) (cat : is-category C) → make-subobject-classifier fc cat → Subobject-classifier C
  to-subobject-classifier fc cat mk = from-classification fc cat (mk .true) (mk .name) (mk .named-name) (mk .name-named)

Sets-subobject-classifier : ∀ {ℓ} → Subobject-classifier (Sets ℓ)
Sets-subobject-classifier {ℓ} =
  to-subobject-classifier Sets-finitely-complete Sets-is-category mk where
  open Subr (Sets-pullbacks {ℓ})
  open Cat.Prelude using (Ω)
  open make-subobject-classifier hiding (Ω)
```
-->

The prototypical category with a subobject classifier is the category of
sets. Since it is finitely complete and univalent, our helper above will
let us swiftly dispatch the construction. Our subobject classifier is
given by the type of propositions, $\Omega$, lifted to the right
universe. The name of a subobject $m : \Sub(A)$ is the family of
propositions $x \mapsto m^*(x)$. Note that we must squash this fibre
down so it fits in $\Omega$, but this squashing is benign because $m$ is
a monomorphism (hence, an embedding).


```agda
  unbox : ∀ {A : Set ℓ} (m : Subobject A) {x} → □ (fibre (m .map) x) → fibre (m .map) x
  unbox m = □-out (monic→is-embedding (hlevel 2) (λ {C} g h p → m .monic {C} g h p) _)

  mk : make-subobject-classifier _ _
  mk .make-subobject-classifier.Ω = el! (Lift _ Ω)
  mk .true _ = lift ⊤Ω
  mk .name m x = lift (elΩ (fibre (m .map) x))
```

Showing that this `name`{.Agda} function actually works takes a bit of
fiddling, but it's nothing outrageous.

```agda
  mk .named-name m = Sub-antisym
    record
      { map = λ w → m .map w , lift tt , ap lift (to-is-true (inc (w , refl)))
      ; com = refl
      }
    record { com = ext λ x _ p → sym (unbox m (from-is-true p) .snd )}
  mk .name-named h = ext λ a → Ω-ua
    (rec! λ x _ p y=a → from-is-true (ap h (sym y=a) ∙ p))
    (λ ha → inc ((a , lift tt , ap lift (to-is-true ha)) , refl))
```

## As generic objects

We can connect the definition above with that of [[generic objects]] in
a [[fibration]]: specifically, a generic subobject is a generic object
in the fibration of subobjects. The similar naming is not an accident:
the proof boils down to shuffling data around.

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ)  where
  open is-generic-subobject
  open is-pullback-along
  open Generic-object
  open Cat.Reasoning C using (pulll)
  open is-cartesian
  open Subobjs C
```
-->

```agda
  from-generic-subobject
    : ∀ {Ω} {tru : Subobject Ω} → is-generic-subobject C tru
    → Generic-object Subobjects tru
  from-generic-subobject gen .classify    = gen .name
  from-generic-subobject gen .classify' s = record { com = gen .classifies s .square }
  from-generic-subobject gen .classify-cartesian s = record
    { universal = λ {u} {u'} m a → record
      { map = gen .classifies s .universal (pulll refl ∙ a .com)
      ; com = sym (gen .classifies s .p₁∘universal)
      }
    ; commutes  = λ m h → prop!
    ; unique    = λ m h → prop!
    }
```

<!--
```agda
open Subobject-classifier using (unique)

module props {o ℓ} {C : Precategory o ℓ} (pb : has-pullbacks C) (so : Subobject-classifier C) where
  open Subobject-classifier so renaming (Ω to Ω')
  open is-pullback-along
  open Cat.Reasoning C
  open is-invertible
  open is-pullback
  open Pullback
  open Subr pb

  named : ∀ {A} (f : Hom A Ω') → Subobject A
  named f = f ^* true

  named-name : ∀ {A} {m : Subobject A} → m ≅ₘ named (name m)
  named-name = is-pullback-along→iso (classifies _)

  name-named : ∀ {A} {f : Hom A Ω'} → name (named f) ≡ f
  name-named {f = f} = sym $ so .unique record
    { top = pb f (Subobjs.map true) .p₂
    ; has-is-pb = has-is-pb (pb f (true .map))
    }

  name-injective : ∀ {A} {m n : Subobject A} → name m ≡ name n → m ≅ₘ n
  name-injective {m = m} {n} p =
    m              Sub.≅⟨ named-name ⟩
    named (name m) Sub.≅⟨ path→iso (ap named p) ⟩
    named (name n) Sub.≅˘⟨ named-name ⟩
    n              Sub.≅∎

  name-ap : ∀ {A} {m n : Subobject A} → m ≅ₘ n → name m ≡ name n
  name-ap {m = m} im = so .unique record
    { top       = classifies m .top ∘ im .Sub.from .map
    ; has-is-pb = subst-is-pullback (sym (im .Sub.from .com) ∙ eliml refl) refl refl refl
        (is-pullback-iso (≅ₘ→iso im) (classifies m .has-is-pb))
    }

  named-injective : ∀ {A} {f g : Hom A Ω'} → named f ≅ₘ named g → f ≡ g
  named-injective {f = f} {g = g} p =
    f              ≡˘⟨ name-named ⟩
    name (named f) ≡⟨ name-ap p ⟩
    name (named g) ≡⟨ name-named ⟩
    g ∎

  Ω-unique₂
    : ∀ {A} {f g : Hom A Ω'}
    → is-pullback-along C (named g .map) f (true .map)
    → f ≡ g
  Ω-unique₂ {f = f} {g = g} pb = so .unique pb ∙ name-named

  is-total : ∀ {A} (f : Hom A Ω') → Type _
  is-total f = is-invertible (pb f (true .map) .p₁)

  factors→is-total : ∀ {A} {f : Hom A Ω'} → Factors f (true .map) → is-total f
  factors→is-total (h , p) .inv = pb _ _ .universal (idr _ ∙ p)
  factors→is-total (h , p) .inverses = record
    { invl = pb _ _ .p₁∘universal
    ; invr = Pullback.unique₂ (pb _ _) {p = pushl p}
      (pulll (pb _ _ .p₁∘universal) ∙ idl _)
      (pulll (pb _ _ .p₂∘universal))
      (idr _)
      (idr _ ∙ true .monic _ _ (sym (pulll (sym p) ∙ pb _ (true .map) .square)))
    }

  is-total→factors : ∀ {A} {f : Hom A Ω'} → is-total f → Factors f (true .map)
  is-total→factors {f = f} inv = record { snd = done } where
    rem₁ : is-pullback-along C id f (true .map)
    rem₁ = record { has-is-pb = record
      { square       = idr _ ∙ sym (pulll (sym (pb _ _ .square)) ∙ cancelr (inv .is-invertible.invl))
      ; universal    = λ {P'} {p₁'} _ → p₁'
      ; p₁∘universal = idl _
      ; p₂∘universal = λ {P'} {p₁'} {p₂'} {α} → true .monic _ _ $
          pulll (pulll (sym (pb _ _ .square)) ∙ cancelr (inv .is-invertible.invl))
        ∙ α
      ; unique       = λ p _ → introl refl ∙ p
      }}

    done =
      f                              ≡⟨ so .unique rem₁ ⟩
      name ⊤ₘ                        ≡⟨ intror refl ⟩
      name ⊤ₘ ∘ id                   ≡⟨ classifies ⊤ₘ .square ⟩
      true .map ∘ classifies ⊤ₘ .top ∎

  true-domain-is-terminal : is-terminal C (true .dom)
  true-domain-is-terminal .is-terminal.! = classifies ⊤ₘ .top
  true-domain-is-terminal .is-terminal.!-unique h =
    true .monic h (classifies ⊤ₘ .top)
    $ snd $ is-total→factors
    $ make-invertible (pb _ _ .universal (pullr refl))
      (pb _ _ .p₁∘universal)
      (Pullback.unique₂ (pb _ _) {p = pullr refl}
        (pulll (pb _ _ .p₁∘universal))
        (extendl (pb _ _ .p₂∘universal))
        id-comm
        (true .monic _ _ (extendl (sym (pb _ _ .square)) ∙ pullr (ap (h ∘_) id-comm))))
```
-->
