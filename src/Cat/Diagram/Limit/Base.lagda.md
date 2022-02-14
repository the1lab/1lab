```agda
open import Cat.Diagram.Terminal
open import Cat.Prelude

import Cat.Morphism

module Cat.Diagram.Limit.Base where
```

# Idea

The idea of limits generalises many concrete constructions in
mathematics - from several settings, such as set theory, topology and
algebra - to arbitrary categories. A limit, _if it exists_, is "the best
solution" to an "equational problem". For a first intuition, we can
build them graphically, working directly "on top" of a diagram.

## Products

**Note**: Products are described explicitly in
[`Cat.Diagram.Product`]. The description there might be easier to parse.

[`Cat.Diagram.Product`]: Cat.Diagram.Product.html

Consider a _discrete_ diagram - one that has no interesting morphisms,
only identities, such as the collection of objects below.

~~~{.quiver .short-2}
\[\begin{tikzcd}
A & B
\end{tikzcd}\]
~~~

To consider a limit for this diagram, we first have to go through an
intermediate step - a `Cone`{.Agda}. Draw a new object, the
`apex`{.Agda} - let's call it $P$ - and a family of maps from $P$ "down
onto" all of the objects of the diagram. The new maps have to make
everything in sight commute, but in the case of a discrete diagram, we
can pick any maps. There are no obligations.

~~~{.quiver .short-1}
\[\begin{tikzcd}
  & P \\
  A && B
  \arrow["\pi_1"', from=1-2, to=2-1]
  \arrow["\pi_2", from=1-2, to=2-3]
\end{tikzcd}\]
~~~

It'll be helpful to think of the maps as projections - which is why
they're labelled with the greek letter $\pi$, for **p**rojection.
However, for an arbitrary cone, the maps are.. well, arbitrary.  To
consider a concrete example, we can pretend our diagram was in
$\mathrm{Set}$ all along, and that $A$ was the set $\mathbb{Q}$ and $B$
was the set $\mathbb{R}$. Then the following is a cone over it:

~~~{.quiver .short-1}
\[\begin{tikzcd}
  & {\mathbb{N}} \\
  {\mathbb{Q}} && {\mathbb{R}}
  \arrow["{x \mapsto x}"', hook, from=1-2, to=2-1]
  \arrow["{x \mapsto \sqrt{x}}", from=1-2, to=2-3]
\end{tikzcd}\]
~~~

Abstracting again, there is a canonical definition of _cone homomorphism_ - 
A map between the apices that makes everything in sight commute. If $P'$
and $P$ were both apices for our original discrete diagram, we would
draw a cone homomorphism $f : P' \to P$ as the dashed arrow in following
commutative Starfleet comms badge.

~~~{.quiver .tall-2}
\[\begin{tikzcd}
  & {P'} \\
  \\
  & P \\
  A && B
  \arrow["{f}"{description}, dashed, from=1-2, to=3-2]
  \arrow["{\pi_1}", from=3-2, to=4-1]
  \arrow["{\pi_2}"', from=3-2, to=4-3]
  \arrow[curve={height=6pt}, from=1-2, to=4-1]
  \arrow[curve={height=-6pt}, from=1-2, to=4-3]
\end{tikzcd}\]
~~~

These assemble into a category, `Cones`{.agda}, with composition and
identity given by the composition and identity of ambient category. A
`Limit`{.agda} is, then, a [terminal object] in this category. For $P$
to be a limit in our diagram above, we require that, for any other cone
$P'$ there exists a _unique_ arrow $P' \to P$ that makes everything
commute.

[terminal object]: Cat.Diagram.Terminal.html

The limit over a discrete diagram is called a **product**, and it's
important to note that the diagram need not be finite. Here are concrete
examples of products in categories:

- In $\mathrm{Sets}$, the limit is the _Cartesian product_ of the objects
of the diagram, and the arrows are the projections onto the factors.

- In $\mathrm{Top}$, the limit is the _product space_ of the objects,
and the arrows are projections, considered as continuous maps. The
product topology can be defined as the coarsest topology that makes the
projections continuous.

- In a partially ordered set, considered as a category, the limit is the
_greatest lower bound_ of the objects - In a poset, we consider that
there exists a map $a \to b$ whenever $a \le b$.

  Normalising the definition of limit slightly, it's works out to be an
  object $p$ such that $p \le a$ and $p \le b$, and if there are any
  other $p'$s satisfying that, then $p' \le p$.

This last example also demonstrates that, while we can always _describe_
the limit over a diagram, it does not necessarily exist. Consider the
poset $(\mathbb{R} \setminus {0}, \le)$ of real numbers except zero,
with the usual ordering. Then the product indexed by $\{ x \in
\mathbb{R} : x > 0 \}$ - which is normally $0$ - does not exist. Not
every category has every limit. Some categories have no limits at all!
If a category has every limit, it's called _complete_. 

## Terminal objects

**Note**: Terminal objects are described explicitly in
[`Cat.Diagram.Terminal`]. The description there might be easier to
parse.

[`Cat.Diagram.Terminal`]: Cat.Diagram.Terminal.html

Perhaps a simpler example of a limit is the one over the empty diagram.
Since the empty diagram is discrete, what we'll end up with is a kind of
product - an empty product. A cone over the empty diagram is an object -
the family of maps, indexed over the objects of the diagram, is empty.

In this case, a cone homomorphism works out to be a regular ol'
morphism, so the terminal object in the cone category is a terminal
object in the ambient category: an object $\top$ such that, for every
other $A$, there's a unique arrow $A \to \top$.

# Construction

Cones are always considered over a _diagram_. Diagram just means
"functor", but it's a concept with an attitude: Whereas, in general,
functors can be a lot more involved than the name "diagram" would
suggest, _every_ functor can be considered a diagram! However, for the
purpose of constructing limits, we generally work with functors out of
"shapes", tiny categories like $\bullet \to \bullet \leftarrow \bullet$.

<!--
```agda
private variable
  o₁ o₂ h₁ h₂ : Level
```
-->

```agda
module _ {J : Precategory o₁ h₁} {C : Precategory o₂ h₂} (F : Functor J C) where
  private
    import Cat.Reasoning J as J
    import Cat.Reasoning C as C
    module F = Functor F

  record Cone : Type (o₁ ⊔ o₂ ⊔ h₁ ⊔ h₂) where
    no-eta-equality
```

A `Cone`{.Agda} over $F$ is given by an object (the `apex`{.agda})
together with a family of maps `ψ`{.Agda} --- one for each object in the
indexing category `J`{.Agda} --- such that "everything in sight
commutes".

```agda
    field
      apex     : C.Ob
      ψ        : (x : J.Ob) → C.Hom apex (F.₀ x)
```

For every map $f : x \to y$ in the indexing category, we require that
the diagram below commutes. This encompasses "everything" since the only
non-trivial composites that can be formed with the data at hand are of
the form $F(f) \circ \psi_x$.

```agda
      commutes : ∀ {x y} (f : J.Hom x y) → F.₁ f C.∘ ψ x ≡ ψ y
```

These non-trivial composites consist of following the left leg of the
diagram below, followed by the bottom leg. For it to commute, that path
has to be the same as following the right leg.

~~~{.quiver .short-05}
\[\begin{tikzcd}
  & {\operatorname{apex}} \\
  {F(x)} && {F(y)}
  \arrow["{F(f)}"', from=2-1, to=2-3]
  \arrow["{\psi_x}"', from=1-2, to=2-1]
  \arrow["{\psi_y}", from=1-2, to=2-3]
\end{tikzcd}\]
~~~

Since paths in Hom-spaces `are propositions`{.Agda ident=Hom-set}, to
test equality of cones, it suffices for the apices to be equal, and for
their $\psi$s to assign equal morphisms for every object in the shape
category.

```agda
  Cone≡ : {x y : Cone}
        → (p : Cone.apex x ≡ Cone.apex y)
        → (∀ o → PathP (λ i → C.Hom (p i) (F.₀ o)) (Cone.ψ x o) (Cone.ψ y o))
        → x ≡ y
  Cone≡ p q i .Cone.apex = p i
  Cone≡ p q i .Cone.ψ o = q o i
  Cone≡ {x = x} {y} p q i .Cone.commutes {x = a} {y = b} f = 
    isProp→PathP (λ i → C.Hom-set _ _ (F.₁ f C.∘ q a i) (q b i)) 
      (x .commutes f) (y .commutes f) i
    where open Cone
```

## Cone maps

```agda
  record ConeHom (x y : Cone) : Type (o₁ ⊔ h₂) where
    no-eta-equality
```

A `Cone homomorphism`{.Agda ident="ConeHom"} is -- like the introduction
says -- a map `hom`{.Agda} in the ambient category between the apices,
such that "everything in sight `commutes`{.Agda ident="ConeHom.commutes"}".  
Specifically, for any choice of object $o$ in the index category, the
composition of `hom`{.Agda} with the domain cone's `ψ`{.Agda} (at that
object) must be equal to the codomain's `ψ`{.Agda}.


```agda
    field
      hom      : C.Hom (Cone.apex x) (Cone.apex y)
      commutes : ∀ {o} → Cone.ψ y o C.∘ hom ≡ Cone.ψ x o
```

<!--
```agda
  ConeHom≡ : ∀ {x y} {f g : ConeHom x y} → ConeHom.hom f ≡ ConeHom.hom g → f ≡ g
  ConeHom≡ p i .ConeHom.hom = p i
  ConeHom≡ {x = x} {y} {f} {g} p i .ConeHom.commutes {o} j = 
    isSet→SquareP (λ i j → C.Hom-set _ _)
      (λ j → Cone.ψ y o C.∘ p j) (f .ConeHom.commutes) (g .ConeHom.commutes) refl i j
```
-->

Since cone homomorphisms are morphisms in the underlying category with
extra properties, we can lift the laws from the underlying category to
the category of `Cones`{.Agda}. The definition of `compose`{.Agda} is the
enlightening part, since we have to prove that two cone homomorphisms
again preserve _all_ the commutativities. 

```agda
  Cones : Precategory _ _
  Cones = cat where
    open Precategory

    compose : {x y z : _} → ConeHom y z → ConeHom x y → ConeHom x z
    compose {x} {y} {z} F G = r where
      open ConeHom
      r : ConeHom x z
      r .hom = hom F C.∘ hom G
      r .commutes {o} =
        Cone.ψ z o C.∘ hom F C.∘ hom G ≡⟨ C.pulll (commutes F) ⟩
        Cone.ψ y o C.∘ hom G           ≡⟨ commutes G ⟩
        Cone.ψ x o                     ∎

    cat : Precategory _ _
    cat .Ob = Cone
    cat .Hom = ConeHom
    cat .id = record { hom = C.id ; commutes = C.idr _ }
    cat ._∘_ = compose
    cat .idr f = ConeHom≡ (C.idr _)
    cat .idl f = ConeHom≡ (C.idl _)
    cat .assoc f g h = ConeHom≡ (C.assoc _ _ _)
```

<!--
```agda
    cat .Hom-set x y = isHLevel-retract 2 pack unpack pack∘unpack hl
      where abstract
        T : Type (o₁ ⊔ h₂)
        T = Σ[ hom ∈ C.Hom (Cone.apex x) (Cone.apex y) ] 
              (∀ o → Cone.ψ y o C.∘ hom ≡ Cone.ψ x o)

        pack : T → ConeHom x y
        pack x = record { hom = x .fst ; commutes = x .snd _ }

        unpack : ConeHom x y → T
        unpack r = r .ConeHom.hom , λ _ → r .ConeHom.commutes

        pack∘unpack : isLeftInverse pack unpack
        pack∘unpack x i .ConeHom.hom = x .ConeHom.hom
        pack∘unpack x i .ConeHom.commutes = x .ConeHom.commutes

        hl : isSet T
        hl = isHLevelΣ 2 (C.Hom-set _ _) 
              (λ _ → isHLevelΠ 2 λ _ → isProp→isSet (C.Hom-set _ _ _ _))
```
-->

## Limits

At risk of repeating myself: *A `Limit`{.agda} is, then, a [terminal
object] in this category.*

[terminal object]: Cat.Diagram.Terminal.html

```agda
  Limit : Type _
  Limit = Terminal Cones

  Limit-apex : Limit → C.Ob
  Limit-apex x = Cone.apex (Terminal.top x)
```

<!--
```agda
module _ {o₁ h₁ o₂ h₂ o₃ h₃ : _}
         {J : Precategory o₁ h₁}
         {C : Precategory o₂ h₂}
         {D : Precategory o₃ h₃}
         {Dia : Functor J C}
         (F : Functor C D)
  where

  private
    module D = Precategory D
    module C = Precategory C
    module J = Precategory J
  
  open Functor
```
-->

# Preservation of limits

Since a cone is, in particular, a commutative diagram, and every functor
preserves commutativity of diagrams, a functor $F : \ca{C} \to \ca{D}$ 
acts on a cone over $\mathrm{Dia}$ (in $\ca{C}$), sending it to a cone
over $F \circ \mathrm{Dia}$ (in $\ca{D}$).

```agda
  F-map-Cone : Cone Dia → Cone (F F∘ Dia)
  Cone.apex (F-map-Cone x) = F₀ F (Cone.apex x)
  Cone.ψ (F-map-Cone x) x₁ = F₁ F (Cone.ψ x x₁)
  Cone.commutes (F-map-Cone x) {y = y} f =
      F₁ F (F₁ Dia f) D.∘ F₁ F (Cone.ψ x _) ≡⟨ sym (F-∘ F _ _) ⟩
      F₁ F (F₁ Dia f C.∘ Cone.ψ x _)        ≡⟨ ap (F₁ F) (Cone.commutes x _) ⟩
      F₁ F (Cone.ψ x y)                     ∎
```

Suppose you have a limit $L$ of $\mathrm{Dia}$ --- which is, to
reiterate, a terminal object in the category of cones over
$\mathrm{Dia}$. We say that $F$ *preserves $L$* if $F(L)$, as defined
right above, is a terminal object in the category of cones over 
$F \circ \mathrm{Dia}$.

```
  PreservesLimit : Limit Dia → Type _
  PreservesLimit o = isTerminal (Cones (F F∘ Dia)) (F-map-Cone (Terminal.top o))
```

This definition is necessary because $\ca{D}$ will not, in general,
possess an operation assigning a limit to every diagram --- therefore,
there might not be a "canonical limit" of $F\circ\mathrm{Dia}$ we could
compare $F(L)$ to. However, since limits are described by a universal
property (in particular, being terminal), we don't _need_ such an
object! Any limit is as good as any other.

## Continuity

```agda
Continuous 
  : ∀ {oshape hshape} 
      {C : Precategory o₁ h₁} 
      {D : Precategory o₂ h₂}
  → Functor C D → Type _
```

A continuous functor is one that --- for every shape of diagram `J`, and
every diagram `diagram`{.Agda} of shape `J` in `C` --- preserves the
limit for that diagram.

```agda
Continuous {oshape = oshape} {hshape} {C = C} F = 
  ∀ {J : Precategory oshape hshape} {diagram : Functor J C}
  → (L : Limit diagram) → PreservesLimit F L
```

<!--
```agda
_ = ConeHom.commutes
```
-->

# Uniqueness

<!--
```agda
module _ {o₁ h₁ o₂ h₂ : _} {J : Precategory o₁ h₁} {C : Precategory o₂ h₂}
         (F : Functor J C)
       where
  private
    module J = Precategory J
    module C = Cat.Morphism C
    module F = Functor F
    module Cones = Cat.Morphism (Cones F)
```
-->

Above, there has been mention of _the_ limit. The limit of a diagram, if
it exists, is unique up to isomorphism. We prove that here. The argument
is as follows: Fixing a diagram $F$, suppose that $X$ and $Y$ are both
limiting cones for for $F$.

```agda
  Limiting-cone-unique 
    : (X Y : Limit F)
    → Terminal.top X Cones.≅ Terminal.top Y
  Limiting-cone-unique X Y = Cones.makeIso f g f∘g≡id g∘f≡id where
    X-cone = Terminal.top X
    Y-cone = Terminal.top Y
```

It follows from $Y$ (resp. $X$) being a terminal object that there is a
unique cone homomorphism $f : X \to Y$ (resp $g : Y \to X$).

```
    f : Cones.Hom X-cone Y-cone
    f = Terminal.! Y {X-cone}

    g : Cones.Hom Y-cone X-cone
    g = Terminal.! X {Y-cone}
```

To show that $g$ is an inverse to $f$, consider the composition $g \circ
f$ (the other case is symmetric): It is a map $g \circ f : X \to X$.
Since $X$ is a terminal object, we have that the space of cone
homomorphisms $X \to X$ is contractible - and thus any two such maps are
equal. Thus, $g \circ f = \mathrm{id}_{X} : X \to X$.

```agda
    f∘g≡id : (f Cones.∘ g) ≡ Cones.id
    f∘g≡id = Terminal.!-unique₂ Y (f Cones.∘ g) Cones.id

    g∘f≡id : (g Cones.∘ f) ≡ Cones.id
    g∘f≡id = Terminal.!-unique₂ X (g Cones.∘ f) Cones.id
```

There is an evident functor from `Cones`{.Agda} to `C`, which sends
cones to their apices and cone homomorphisms to their underlying maps.
Being a functor, it preserves isomorphisms, so we get an isomorphism of
the limit _objects_ from the isomorphism of limit _cones_.

Contrary to the paragraph above, though, rather than defining a functor,
there is a direct proof that an isomorphism of limits results in an
isomorphism of apices. Fortunately, the direct proof
`Cone≅→apex≅`{.Agda} is exactly what one would get had they defined the
functor and used the proof that it preserves isomorphisms.

```agda
  Cone≅→apex≅ : {X Y : Cone F}
              → X Cones.≅ Y
              → (Cone.apex X) C.≅ (Cone.apex Y)
  Cone≅→apex≅ c = 
    C.makeIso (ConeHom.hom c.to) (ConeHom.hom c.from)
      (ap ConeHom.hom c.invˡ)
      (ap ConeHom.hom c.invʳ)
    where module c = Cones._≅_ c

  Limit-unique 
    : {X Y : Limit F}
    → Cone.apex (Terminal.top X) C.≅ Cone.apex (Terminal.top Y)
  Limit-unique {X} {Y} = Cone≅→apex≅ (Limiting-cone-unique X Y)
```
