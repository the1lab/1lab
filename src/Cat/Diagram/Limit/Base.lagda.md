```agda
open import Cat.Functor.Coherence
open import Cat.Functor.Kan.Base
open import Cat.Functor.Kan.Unique
open import Cat.Instances.Functor
open import Cat.Instances.Shape.Terminal
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Reasoning

module Cat.Diagram.Limit.Base where
```

# Idea

**Note**: This page describes the general definition of limits, and
assumes some familiarity with some concrete examples, in particular
[terminal objects], [products], [equalisers], and [pullbacks]. It might
be a good idea to check out those pages before continuing!

[terminal objects]: Cat.Diagram.Terminal.html
[products]: Cat.Diagram.Product.html
[equalisers]: Cat.Diagram.Equaliser.html
[pullbacks]: Cat.Diagram.Pullback.html

To motivate limits, note how all the above examples have roughly the
same structure. They all consist of some object, a bunch of maps out
of said object, some commuting conditions, and a universal property
that states that we can construct unique maps into the object under
certain conditions.

Our first step towards making this vague intuition precise is to construct
a mathematical widget that picks out a collection of objects, arrows,
and commutation conditions in a category. This is required to describe
the collection of maps out of our special objects, and the equations
they satisfy. Luckily, we already have such a widget: functors!

To see how this works, let's take a very simple example: a functor out
of the [single object category with one morphism] into some category
$\cC$. If we look at the image of such a functor, we can see that it
picks out a single object; the single morphism must be taken to the
identity morphism due to functoriality. We can scale this example up
to functors from [discrete category] with $n$ elements; if we look at
the image of such a functor, we shall see that it selects out $n$ objects
of $\cC$.

[single object category with one morphism]: Cat.Instances.Shape.Terminal.html
[discrete category]: Cat.Instances.Discrete.html

We can perform the same trick with non-discrete categories; for instance,
a functor out of the [parallel arrows category] selects a pair of
parallel arrows in $\cC$, a functor out of the [isomorphism category]
selects an isomorphism in $\cC$, and so on. We call such functors
**diagrams** to suggest that we should think of them as picking out some
shape in $\cC$.

[parallel arrows category]: Cat.Instances.Shape.Parallel.html
[isomorphism category]: Cat.Instances.Shape.Isomorphism.html

We can use this newfound insight to describe the shape that each of our
examples is defined over. Products are defined over a diagram that
consists of a pair of objects; these diagrams correspond to functors
out of the category with 2 objects and only identity morphisms.
Equalisers are defined over a diagram that consists of a pair of parallel
morphisms; such diagrams are given by functors out of the aforementioned
parallel arrows category. Pullbacks defined over a diagram of the shape,
$\bullet \to \bullet \leftarrow \bullet$; again, these diagrams are
given by functors out of the category with that exact shape. Terminal
objects may seem to break this trend, but we can think of them as
being defined over the empty diagram, which is given by functors out
of the category with no objects.

We now move our attention to the maps out of our special object into
the objects of the diagram. Note that these maps need to commute with
any morphisms in the diagram, as is the case with pullbacks and
equalisers. This is where our definition diverges from many other
introductory sources. The typical approach is to define a bespoke
widget called a [cone] that encodes the required morphisms and commuting
conditions, and then proceeding from there.

[cone]: Cat.Diagram.Limit.Cone.html

However, this approach is somewhat unsatisfying. Why did we have to
invent a new object just to bundle up the data we needed? Furthermore,
cones are somewhat disconnected from the rest of category theory, which
makes it more difficult to integrate results about limits into the larger
body of work. It would be great if we could encode the data we needed
using existing objects!

Luckily, we can! If we take a step back, we can notice that we are trying
to construct a map into a functor. What are maps into functors? Natural
transformations! Concretely, let $D : \cJ \to cC$ be some diagram.
We can encode the same data as a cone in a natural transformation
$\eta : !x \circ ! \to D$, where $!x : \top \to \cC$ denotes
the constant functor that maps object to $x$ and every morphism to $id$,
and $! : \cJ \to \top$ denotes the unique functor into the terminal
category. The components of such a natural transformation yield maps from
$x \to D(j)$ for every $j : \cJ$, and naturality ensures that these
maps must commute with the rest of the diagram. We can describe this
situation diagrammatically like so:

~~~{.quiver}
\begin{tikzcd}
  && \top \\
  \\
  {\cJ} &&& {} & {\cC}
  \arrow[from=3-1, to=1-3]
  \arrow["{!X}"', from=1-3, to=3-5]
  \arrow[""{name=0, anchor=center, inner sep=0}, from=3-1, to=3-5]
  \arrow["\eta"{description}, shorten <=4pt, shorten >=4pt, Rightarrow, from=1-3, to=0]
\end{tikzcd}
~~~

All that remains is the universal property. If we translate this into
our existing machinery, that means that $!x$ must be the universal
functor equipped with natural transformation $\eta$; that is, for
any other $K : \top \to \cC$ equipped with $\tau : K \circ \to D$, we
have a unique natural transformation $\sigma : K \to !x$ that factorises
$\tau$. This is a bit of a mouthful, so lets look at a diagram instead.

~~~{.quiver}
\begin{tikzcd}
  && \top \\
  \\
  {\cJ} &&& {} & {\cC}
  \arrow[from=3-1, to=1-3]
  \arrow[""{name=0, anchor=center, inner sep=0}, "{!x}"', from=1-3, to=3-5]
  \arrow[""{name=1, anchor=center, inner sep=0}, from=3-1, to=3-5]
  \arrow[""{name=2, anchor=center, inner sep=0}, "K", curve={height=-18pt}, from=1-3, to=3-5]
  \arrow["\eta"{description}, shorten <=4pt, shorten >=4pt, Rightarrow, from=1-3, to=1]
  \arrow["\sigma", shorten <=3pt, shorten >=3pt, Rightarrow, from=2, to=0]
\end{tikzcd}
~~~

We might be tempted to stop here and call it a day, but we can go one
step further. It turns out that these universal functors have a name:
they are [right kan extensions]. This allows for an extremely concise
definition of limits: $x : \cC$ is the limit of a diagram
$D : \cJ \to \cC$ when the constant functor $!x : \top \to \cC$ is
a right kan extension of $! : \cJ \to \top$ along $D$.

[right kan extensions]: Cat.Functor.Kan.Right.html

<!--
```agda
private variable
  o₁ o₂ o₃ h₁ h₂ h₃ : Level
```
-->

```agda
module _ {J : Precategory o₁ h₁} {C : Precategory o₂ h₂} (Diagram : Functor J C) where
  private
    module C = Precategory C

  cone→counit : ∀ {x : C.Ob} → (Const x => Diagram) → const! x F∘ !F => Diagram
  unquoteDef cone→counit = define-coherence cone→counit

  is-limit : (x : C.Ob) → Const x => Diagram → Type _
  is-limit x cone = is-ran !F Diagram (const! x) (cone→counit cone)
```

Furthermore, we say $D$ has a limit if there exists some right kan extension
of $!$ along $D$.

```agda
  Limit : Type _
  Limit = Ran !F Diagram
```

## Concretely

The definition above is very concise, and it has the benefit of being
abstract: We can re-use definitions and theorems originally stated for
Kan extensions to limits. However, it has the downside of being
abstract: it's good for working with _limits in general_, but working
with a _specific_ limit is penalised, as the data we want to get at is
"buried".

The definition above is also hard to _instantiate_, since you have to..
bury the data, and some of it is really quite deep! What we do is
provide an auxiliary record, `make-is-limit`{.Agda}, which computes
right extensions to the point.

<!--
```agda
module _ {J : Precategory o₁ h₁} {C : Precategory o₂ h₂}
  where
  private
    module J = Precategory J
    module C = Cat.Reasoning C

  record make-is-limit (Diagram : Functor J C) (apex : C.Ob)
            : Type (o₁ ⊔ h₁ ⊔ o₂ ⊔ h₂) where
    no-eta-equality
    open Functor Diagram
```
-->

We solve this by defining a _concretised_ version of `is-limit`{.Agda},
called `make-is-limit`{.Agda}, which exposes the following data. First,
we have morphisms from the apex to every value in the diagram, a family
called $\psi$. Moreover, if $f : x \to y$ is a morphism in the "shape"
category $\cJ$, then $Ff\psi x = \psi y$, i.e., the $\psi$ maps fit into
triangles

~~~{.quiver .tall-15}
\[\begin{tikzcd}
  & {\mathrm{apex}} \\
  \\
  Fx && {Fy\text{.}}
  \arrow["{\psi_x}"', curve={height=6pt}, from=1-2, to=3-1]
  \arrow["{\psi_y}", curve={height=-6pt}, from=1-2, to=3-3]
  \arrow["Ff"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

```agda
    field
      ψ        : (j : J.Ob) → C.Hom apex (F₀ j)
      commutes : ∀ {x y} (f : J.Hom x y) → F₁ f C.∘ ψ x ≡ ψ y
```

The rest of the data says that $\psi$ is the universal family of maps
with this property: If $\eta_j : x \to Fj$ is another family of maps
with the same commutativty property, then each $\eta_j$ factors through
the apex by a single, _unique_ universal morphism:

```agda
      universal
        : ∀ {x : C.Ob}
        → (eta : ∀ j → C.Hom x (F₀ j))
        → (∀ {x y} (f : J.Hom x y) → F₁ f C.∘ eta x ≡ eta y)
        → C.Hom x apex

      factors
        : ∀ {j : J.Ob} {x : C.Ob}
        → (eta : ∀ j → C.Hom x (F₀ j))
        → (p : ∀ {x y} (f : J.Hom x y) → F₁ f C.∘ eta x ≡ eta y)
        → ψ j C.∘ universal eta p ≡ eta j

      unique
        : ∀ {x : C.Ob}
        → (eta : ∀ j → C.Hom x (F₀ j))
        → (p : ∀ {x y} (f : J.Hom x y) → F₁ f C.∘ eta x ≡ eta y)
        → (other : C.Hom x apex)
        → (∀ j → ψ j C.∘ other ≡ eta j)
        → other ≡ universal eta p
```

<!--
```agda
    unique₂
      : ∀ {x : C.Ob}
      → (eta : ∀ j → C.Hom x (F₀ j))
      → (p : ∀ {x y} (f : J.Hom x y) → F₁ f C.∘ eta x ≡ eta y)
      → {o1 : C.Hom x apex} → (∀ j → ψ j C.∘ o1 ≡ eta j)
      → {o2 : C.Hom x apex} → (∀ j → ψ j C.∘ o2 ≡ eta j)
      → o1 ≡ o2
    unique₂ {x = x} eta p q r = unique eta p _ q ∙ sym (unique eta p _ r)
```
-->

If we have this data, then we can make a value of `is-limit`{.Agda}. It
might seem like naturality, required for a Kan extension, is missing
from `make-is-limit`{.Agda}, but it can be derived from the other data
we have been given:

<!--
```agda
  open _=>_

  to-cone : ∀ {D : Functor J C} {apex} → make-is-limit D apex → Const apex => D
  to-cone ml .η = ml .make-is-limit.ψ
  to-cone ml .is-natural x y f = C.idr _ ∙ sym (ml .make-is-limit.commutes f)
```
-->

```agda
  to-is-limit : ∀ {D : Functor J C} {apex}
              → (mk : make-is-limit D apex)
              → is-limit D apex (to-cone mk)
  to-is-limit {Diagram} {apex} mklim = lim where
    open make-is-limit mklim
    open is-ran
    open Functor
    open _=>_

    lim : is-limit Diagram apex (to-cone mklim)
    lim .σ {M = M} α .η _ =
      universal (α .η) (λ f → sym (α .is-natural _ _ f) ∙ C.elimr (M .F-id))
    lim .σ {M = M} α .is-natural _ _ _ =
      lim .σ α .η _ C.∘ M .F₁ tt ≡⟨ C.elimr (M .F-id) ⟩
      lim .σ α .η _              ≡˘⟨ C.idl _ ⟩
      C.id C.∘ lim .σ α .η _     ∎
    lim .σ-comm {β = β} = Nat-path λ j →
      factors (β .η) _
    lim .σ-uniq {β = β} {σ′ = σ′} p = Nat-path λ _ →
      sym $ unique (β .η) _ (σ′ .η tt) (λ j → sym (p ηₚ j))
```

<!--
```agda
  to-is-limitp
    : ∀ {D : Functor J C} {K : Functor ⊤Cat C} {eps : K F∘ !F => D}
    → (mk : make-is-limit D (Functor.F₀ K tt))
    → (∀ {j} → to-cone mk .η j ≡ eps .η j)
    → is-ran !F D K eps
  to-is-limitp {D} {K} {eps} mklim p = lim where
    open make-is-limit mklim
    open is-ran
    open Functor
    open _=>_

    lim : is-ran !F D K eps
    lim .σ {M = M} α .η _ =
      universal (α .η) (λ f → sym (α .is-natural _ _ f) ∙ C.elimr (M .F-id))
    lim .σ {M = M} α .is-natural _ _ _ =
      C.elimr (M .F-id) ∙ C.introl (K .F-id)
    lim .σ-comm {β = β} = Nat-path λ j →
      ap (C._∘ _) (sym p) ∙ factors (β .η) _
    lim .σ-uniq {β = β} {σ′ = σ′} q = Nat-path λ _ →
      sym (unique (β .η) _ (σ′ .η tt) λ j → ap (C._∘ _) p ∙ sym (q ηₚ j))
```
-->

To _use_ the data of `is-limit`, we provide a function for *un*making a
limit:

```agda
  unmake-limit
    : ∀ {D : Functor J C} {F : Functor ⊤Cat C} {eps}
    → is-ran !F D F eps
    → make-is-limit D (Functor.F₀ F tt)
  unmake-limit {D} {F} {eps = eps} lim = ml module unmake-limit where
    a = Functor.F₀ F tt
    module eps = _=>_ eps
    open is-ran lim
    open Functor D
    open make-is-limit
    open _=>_

    module _ {x} (eta : ∀ j → C.Hom x (F₀ j))
                 (p : ∀ {x y} (f : J.Hom x y) → F₁ f C.∘ eta x ≡ eta y)
      where

      eta-nt : const! x F∘ !F => D
      eta-nt .η = eta
      eta-nt .is-natural _ _ f = C.idr _ ∙ sym (p f)

      hom : C.Hom x a
      hom = σ {M = const! x} eta-nt .η tt

    ml : make-is-limit D a
    ml .ψ j        = eps.η j
    ml .commutes f = sym (eps.is-natural _ _ f) ∙ C.elimr (Functor.F-id F)

    ml .universal   = hom
    ml .factors e p = σ-comm {β = eta-nt e p} ηₚ _
    ml .unique {x = x} eta p other q =
      sym $ σ-uniq {σ′ = other-nt} (Nat-path λ j → sym (q j)) ηₚ tt
      where
        other-nt : const! x => F
        other-nt .η _ = other
        other-nt .is-natural _ _ _ = C.idr _ ∙ C.introl (Functor.F-id F) -- C.id-comm
```

<!--
```agda
  to-limit
    : ∀ {D : Functor J C} {apex : C.Ob} {eps : Const apex => D}
    → is-limit D apex eps
    → Limit D
  to-limit l .Ran.Ext = _
  to-limit l .Ran.eps = _
  to-limit l .Ran.has-ran = l
```
-->

<!--
```agda
module is-limit
  {J : Precategory o₁ h₁} {C : Precategory o₂ h₂}
  {D : Functor J C} {F : Functor ⊤Cat C} {eps : F F∘ !F => D}
  (t : is-ran !F D F eps)
  where

  open make-is-limit (unmake-limit {F = F} t) public
```
-->

We also provide a similar interface for the bundled form of limits.

```agda
module Limit
  {J : Precategory o₁ h₁} {C : Precategory o₂ h₂} {D : Functor J C} (L : Limit D)
  where
```

<!--
```agda
  private
    import Cat.Reasoning J as J
    import Cat.Reasoning C as C
    module Diagram = Functor D
    open Ran L
    open Functor
    open _=>_
```
-->

The "apex" object of the limit is the single value in the image of the
extension functor.

```agda
  apex : C.Ob
  apex = Ext.₀ tt
```

Furthermore, we can show that the apex is the limit, in the sense of
`is-limit`{.Agda}, of the diagram. You'd think this is immediate, but
unfortunately proof assistants: `is-limit`{.Agda} asks for _the_
constant functor functor $\{*\} \to \cC$ with value `apex` to be a Kan
extension, but `Limit`{.Agda}, being an instance of `Ran`{.Agda},
packages an _arbitrary_ functor $\{*\} \to \cC$.

Since Agda does not compare functors for $\eta$-equality, we have to
shuffle our data around manually. Fortunately, this isn't a very long
computation.

```agda
  cone : Const apex => D
  cone .η x = eps .η x
  cone .is-natural x y f = ap (_ C.∘_) (sym $ Ext .F-id) ∙ eps .is-natural x y f

  has-limit : is-limit D apex cone
  has-limit .is-ran.σ α .η = σ α .η
  has-limit .is-ran.σ α .is-natural x y f =
    σ α .is-natural tt tt tt ∙ ap (C._∘ _) (Ext .F-id)
  has-limit .is-ran.σ-comm =
    Nat-path (λ _ → σ-comm ηₚ _)
  has-limit .is-ran.σ-uniq {M = M} {σ′ = σ′} p =
    Nat-path (λ _ → σ-uniq {σ′ = nt} (Nat-path (λ j → p ηₚ j)) ηₚ _) where
      nt : M => Ext
      nt .η = σ′ .η
      nt .is-natural x y f = σ′ .is-natural x y f ∙ ap (C._∘ _) (sym $ Ext .F-id)

  open is-limit has-limit public
```

# Uniqueness

<!--
```agda
module _ {o₁ h₁ o₂ h₂ : _} {J : Precategory o₁ h₁} {C : Precategory o₂ h₂}
         {Diagram : Functor J C}
         {x y} {epsy : Const y => Diagram} {epsx : Const x => Diagram}
         (Ly : is-limit Diagram y epsy)
         (Lx : is-limit Diagram x epsx)
       where
  private
    module J = Precategory J
    module C = Cat.Reasoning C
    module Diagram = Functor Diagram
    open is-ran
    open _=>_

    module Ly = is-limit Ly
    module Lx = is-limit Lx
```
-->

Above, there has been mention of _the_ limit. The limit of a diagram, if
it exists, is unique up to isomorphism. We prove that here. The argument
is as follows: Fixing a diagram $F$, suppose that $x$ and $y$ are both
limits of $F$. We can use the universal maps associated with each limit
to construct both directions of the isomorphism. Furthermore, these
are mutually inverse, as universal maps are unique.

We show a slightly more general result first: if there exist a pair of
maps $f$, $g$ between the apexes of the 2 limits, and these maps commute
with the 2 limits, then $f$ and $g$ are inverses.

```agda
  limits→inversesp
    : ∀ {f : C.Hom x y} {g : C.Hom y x}
    → (∀ {j : J.Ob} → Ly.ψ j C.∘ f ≡ Lx.ψ j)
    → (∀ {j : J.Ob} → Lx.ψ j C.∘ g ≡ Ly.ψ j)
    → C.Inverses f g
  limits→inversesp f-factor g-factor =
    C.make-inverses
      (Ly.unique₂ Ly.ψ Ly.commutes (λ j → C.pulll f-factor ∙ g-factor) λ _ → C.idr _)
      (Lx.unique₂ Lx.ψ Lx.commutes (λ j → C.pulll g-factor ∙ f-factor) λ _ → C.idr _)
```

Furthermore, any morphism between apexes that commutes with the limit
must be invertible.

```agda
  limits→invertiblep
    : ∀ {f : C.Hom x y}
    → (∀ {j : J.Ob} → Ly.ψ j C.∘ f ≡ Lx.ψ j)
    → C.is-invertible f
  limits→invertiblep f-factor =
    C.inverses→invertible $
    limits→inversesp f-factor (Lx.factors Ly.ψ Ly.commutes)
```

This implies that the universal maps must also be inverses.

```agda
  limits→inverses
    : C.Inverses (Ly.universal Lx.ψ Lx.commutes) (Lx.universal Ly.ψ Ly.commutes)
  limits→inverses =
    limits→inversesp (Ly.factors Lx.ψ Lx.commutes) (Lx.factors Ly.ψ Ly.commutes)

  limits→invertible
    : C.is-invertible (Ly.universal Lx.ψ Lx.commutes)
  limits→invertible = limits→invertiblep (Ly.factors Lx.ψ Lx.commutes)
```

Finally, we can bundle this data up to show that the apexes are isomorphic.

```agda
  limits-unique : x C.≅ y
  limits-unique = C.invertible→iso _ limits→invertible 
```


Furthermore, if the universal map is invertible, then that means that
its domain is _also_ a limit of the diagram.

<!--
```agda
module _ {o₁ h₁ o₂ h₂ : _} {J : Precategory o₁ h₁} {C : Precategory o₂ h₂}
         {D : Functor J C} {K : Functor ⊤Cat C}
         {epsy : Const (Functor.F₀ K tt) => D}
         (Ly : is-limit D (Functor.F₀ K tt) epsy)
       where
  private
    module J = Precategory J
    module C = Cat.Reasoning C
    module D = Functor D
    open is-ran
    open Functor
    open _=>_

    module Ly = is-limit Ly

  family→cone
    : ∀ {x}
    → (eta : ∀ j → C.Hom x (D.₀ j))
    → (∀ {x y} (f : J.Hom x y) → D.₁ f C.∘ eta x ≡ eta y)
    → Const x => D
  family→cone eta p .η = eta
  family→cone eta p .is-natural _ _ _ = C.idr _ ∙ sym (p _)
```
-->

```agda
  is-invertible→is-limitp
    : ∀ {K' : Functor ⊤Cat C} {eps : K' F∘ !F => D}
    → (eta : ∀ j → C.Hom (K' .F₀ tt) (D.₀ j))
    → (p : ∀ {x y} (f : J.Hom x y) → D.₁ f C.∘ eta x ≡ eta y)
    → (∀ {j} → eta j ≡ eps .η j)
    → C.is-invertible (Ly.universal eta p)
    → is-ran !F D K' eps
  is-invertible→is-limitp {K' = K'} eta p q invert =
    to-is-limitp lim q
    where
      open C.is-invertible invert
      open make-is-limit

      lim : make-is-limit D (K' .F₀ tt)
      lim .ψ = eta
      lim .commutes = p
      lim .universal tau q = inv C.∘ Ly.universal tau q
      lim .factors tau q =
        lim .ψ _ C.∘ inv C.∘ Ly.universal tau q                        ≡˘⟨ Ly.factors eta p C.⟩∘⟨refl ⟩
        (Ly.ψ _ C.∘ Ly.universal eta p) C.∘ inv C.∘ Ly.universal tau q ≡⟨ C.cancel-inner invl ⟩
        Ly.ψ _ C.∘ Ly.universal tau q                                  ≡⟨ Ly.factors tau q ⟩
        tau _                                                          ∎
      lim .unique tau q other r =
        other                                ≡⟨ C.insertl invr ⟩
        inv C.∘ Ly.universal eta p C.∘ other ≡⟨ C.refl⟩∘⟨ Ly.unique _ _ _ (λ j → C.pulll (Ly.factors eta p) ∙ r j) ⟩
        inv C.∘ Ly.universal tau q           ∎
```

Another useful fact is that if $L$ is a limit of some diagram $Dia$, and
$Dia$ is naturally isomorphic to some other diagram $Dia'$, then the
apex of $L$ is also a limit of $Dia'$.

```agda
  natural-iso→is-limitp
    : ∀ {D′ : Functor J C} {eps : K F∘ !F => D′}
    → (isos : natural-iso D D′)
    → (∀ {j} → natural-iso.to isos .η j C.∘ Ly.ψ j ≡ eps .η j)
    → is-ran !F D′ K eps
  natural-iso→is-limitp {D′ = D′} isos p = to-is-limitp lim p where
    open make-is-limit
    module isos = natural-iso isos

    lim : make-is-limit D′ (K .F₀ tt)
    lim .ψ j =  isos.to .η _ C.∘ Ly.ψ j
    lim .commutes f =
      C.pulll (sym $ isos.to .is-natural _ _ f)
      ∙ C.pullr (Ly.commutes f)
    lim .universal eta q =
      Ly.universal
        (λ j → isos.from .η _ C.∘ eta j)
        (λ f →
          C.pulll (sym $ isos.from .is-natural _ _ f)
          ∙ C.pullr (q f))
    lim .factors eta q =
      C.pullr (Ly.factors _ _)
      ∙ C.cancell (isos.invl ηₚ _)
    lim .unique eta q other r =
      Ly.unique _ _ other λ j →
        ap (C._∘ other) (C.insertl (isos.invr ηₚ _)) ∙ C.pullr (r j)
```

<!--
```agda
module _ {o₁ h₁ o₂ h₂ : _} {J : Precategory o₁ h₁} {C : Precategory o₂ h₂}
         {D D′ : Functor J C}
         where

  natural-iso→limit
    : natural-iso D D′
    → Limit D
    → Limit D′
  natural-iso→limit isos L .Ran.Ext = Ran.Ext L
  natural-iso→limit isos L .Ran.eps = natural-iso.to isos ∘nt Ran.eps L
  natural-iso→limit isos L .Ran.has-ran =
    natural-iso→is-limitp (Limit.has-limit L) isos refl
```
-->
 

<!--
```agda
module _ {o₁ h₁ o₂ h₂ : _} {J : Precategory o₁ h₁} {C : Precategory o₂ h₂}
         {Diagram : Functor J C}
         {x} {eps : Const x => Diagram}
         where
  private
    module J = Precategory J
    module C = Cat.Reasoning C
    module Diagram = Functor Diagram
    open is-ran
    open _=>_

  is-limit-is-prop : is-prop (is-limit Diagram x eps)
  is-limit-is-prop = is-ran-is-prop
```
-->

Therefore, if $C$ is a category, then `Limit`{.Agda} is a proposition!
However, this follows from a much more general result about [uniqueness
of kan extensions].

[uniqueness of kan extensions]: Cat.Functor.Kan.Unique.html

<!--
```agda
module _ {o₁ h₁ o₂ h₂ : _} {J : Precategory o₁ h₁} {C : Precategory o₂ h₂}
         {Diagram : Functor J C}
         where
```
-->

```agda
  Limit-is-prop : is-category C → is-prop (Limit Diagram)
  Limit-is-prop cat = Ran-is-prop cat
```


# Preservation of Limits

Suppose you have a limit $L$ of a diagram $\rm{Dia}$. We say that $F$
**preserves $L$** if $F(L)$ is also a limit of $F \circ \rm{Dia}$.

<!--
```agda
module _ {J : Precategory o₁ h₁} {C : Precategory o₂ h₂} {D : Precategory o₃ h₃}
         (F : Functor C D) {Diagram : Functor J C} where
  private
    module D = Precategory D
    module C = Precategory C
    module J = Precategory J
    module F = Func F
```
-->

Suppose you have a limit $L$ of a diagram $\rm{Dia}$. We say that $F$
*preserves $L$* if $F(L)$ is also a limit of $F \circ \rm{Dia}$.

This definition is necessary because $\cD$ will not, in general,
possess an operation assigning a limit to every diagram --- therefore,
there might not be a "canonical limit" of $F\circ\rm{Dia}$ we could
compare $F(L)$ to. However, since limits are described by a universal
property (in particular, being terminal), we don't _need_ such an
object! Any limit is as good as any other.

In more concise terms, we say a functor preserves limits if it takes
limiting cones "upstairs" to limiting cones "downstairs".

```agda
  preserves-limit
    : ∀ {K : Functor ⊤Cat C} {eps : K F∘ !F => Diagram}
    → is-ran !F Diagram K eps
    → Type _
  preserves-limit lim = preserves-ran F lim
```

## Reflection of limits

Using our analogy from before, we say a functor _reflects_ limits
if it takes limiting cones "downstairs" to limiting cones "upstairs".

More concretely, if we have a limit in $\cD$ of $F \circ \rm{Dia}$ with
apex $F(a)$, then $a$ was _already the limit_ of $\rm{Dia}$!

```agda
  reflects-limit
    : ∀ {K : Functor ⊤Cat C} {eps : K F∘ !F => Diagram}
    → is-ran !F (F F∘ Diagram) (F F∘ K) (nat-assoc-from (F ▸ eps))
    → Type _
  reflects-limit ran = reflects-ran F ran
```

## Creation of limits

Finally, we say a functor _creates_ limits of shape $\rm{Dia}$ if it
both preserves _and_ reflects those limits. Intuitively, this means that
the limits of shape $\rm{Dia}$ in $\cC$ are in a 1-1 correspondence
with the limits $F \circ \rm{Dia}$ in $\cD$.

```agda
  -- record creates-limit {K : Functor ⊤Cat} : Type (o₁ ⊔ h₁ ⊔ o₂ ⊔ h₂ ⊔ o₃ ⊔ h₃) where
  --   field
  --     preserves  : preserves-limit
  --     reflectst  : reflects-limit
```

## Continuity

```agda
is-continuous
  : ∀ {oshape hshape}
      {C : Precategory o₁ h₁}
      {D : Precategory o₂ h₂}
  → Functor C D → Type _
```

A continuous functor is one that --- for every shape of diagram `J`, and
every diagram `diagram`{.Agda} of shape `J` in `C` --- preserves the
limit for that diagram.

```agda
is-continuous {oshape = oshape} {hshape} {C = C} F =
  ∀ {J : Precategory oshape hshape} {Diagram : Functor J C}
  → ∀ {K : Functor ⊤Cat C} {eps : K F∘ !F => Diagram}
  → (lim : is-ran !F Diagram K eps)
  → preserves-limit F lim
```

## Completeness

A category is **complete** if admits for limits of arbitrary shape.
However, in the presence of excluded middle, if a category admits
products indexed by its class of morphisms, then it is automatically a
poset. Since excluded middle is independent of type theory, we can not
prove that any non-thin categories have arbitrary limits.

Instead, categories are complete _with respect to_ a pair of universes:
A category is **$(o, \ell)$-complete** if it has limits for any diagram
indexed by a precategory with objects in $\ty\ o$ and morphisms in $\ty\
\ell$.

```agda
is-complete : ∀ {oc ℓc} o ℓ → Precategory oc ℓc → Type _
is-complete o ℓ C = ∀ {D : Precategory o ℓ} (F : Functor D C) → Limit F
```
