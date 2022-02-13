```agda
open import Cat.Prelude

module Cat.Functor.Adjoint where
```

<!--
```agda
private variable
  o h : Level
  C D : Precategory o h

open Functor

adj-level : ∀ {o₁ h₁ o₂ h₂} {C : Precategory o₁ h₁} {D : Precategory o₂ h₂}
          → Functor C D → Functor D C → Level
adj-level {o₁ = o₁} {h₁} {o₂} {h₂} _ _ = o₁ ⊔ o₂ ⊔ h₁ ⊔ h₂
```
-->

# Adjunctions

Category theory is, in general, the study of how things can be related.
For instance, structures at the level of sets (e.g. the collection of
natural numbers) are often interestingly related by propositions (i.e.
the proposition $x \le y$). Structures at the level of groupoids (e.g.
the collection of all sets) are interestingly related by sets (i.e. the
set of maps $x \to y$). Going further, we have structures at the level
of 2-groupoids, which could be given an interesting _category_ of
relations, etc.

A particularly important relationship is, of course, "sameness". Going
up the ladder of category number, we have equality at the (-1)-level,
isomorphism at the 0-level, and what's generally referred to as
"equivalence" at higher levels. It's often interesting to weaken these
relations, by making some components directed: This starts at the level
of categories, where "directing" an equivalence gives us the concept of
**adjunction**.

An _equivalence of categories_ between $\ca{C}$ and $\ca{D}$ is given by
a pair of functors $L : \ca{C} \leftrightarrows \ca{D} : R$, equipped
with natural _isomorphisms_ $\eta : \mathrm{Id} \cong (R \circ L)$ (the
"unit") and $\eps : (L \circ R) \cong \mathrm{Id}$ (the "counit"). We
still want the correspondence to be bidirectional, so we can't change
the types of $R$, $L$; What we _can_ do is weaken the natural
isomorphisms to natural _transformations_. The data of an **adjunction**
starts as such:

```agda
record _⊣_ (L : Functor C D) (R : Functor D C) : Type (adj-level L R) where
  private
    module C = Precategory C
    module D = Precategory D

  field
    unit   : Id => (R F∘ L)
    counit : (L F∘ R) => Id

  module unit = _=>_ unit
  module counit = _=>_ counit renaming (η to ε)
```

Unfortunately, the data that we have here is not particularly coherent.
The `unit`{.Agda} and `counit`{.Agda} let us introduce $R\circ L$ and
eliminate $L\circ R$ in a composition. This gives us two ways of mapping
$L \Rightarrow L$. One is the identity, and the other is going through
the unit: $L \Rightarrow L\circ R\circ L \Rightarrow L$ (the situation
with $R$ is symmetric). We must impose further equations on the natural
transformations to make sure these match:

```agda
  field
    zig : ∀ {x} → F₁ L (unit.η x) D.∘ counit.ε (F₀ L x) ≡ D.id
    zag : ∀ {x} → unit.η (F₀ R x) C.∘ F₁ R (counit.ε x) ≡ C.id
```

These are called "triangle identities" because of the shape they have as
commutative diagrams:

<div class=mathpar>

~~~{.quiver}
\[\begin{tikzcd}
  R & RLR \\
  & R
  \arrow[from=1-1, to=2-2]
  \arrow["{\eta R}", from=1-1, to=1-2]
  \arrow["R\epsilon", from=1-2, to=2-2]
\end{tikzcd}\]
~~~

~~~{.quiver}
\[\begin{tikzcd}
  L & LRL \\
  & L
  \arrow[from=1-1, to=2-2]
  \arrow["L\eta", from=1-1, to=1-2]
  \arrow["{\epsilon L}", from=1-2, to=2-2]
\end{tikzcd}\]
~~~

</div>
