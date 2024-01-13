<!--
```agda
open import Cat.Prelude
open import Cat.Gaunt

import Cat.Reasoning
```
-->

```agda
module Cat.Instances.Free where
```

# Graphs and free categories

A **graph** (really, an $(o, \ell)$-graph^[and, even more pedantically,
a directed multi-$(o, ℓ)$-graph]) is given by a set $V : \Sets_o$ of
**vertices** and, for each pair of elements $x, y : V$, a set of
**edges** $E(x, y) : \Sets_\ell$ from $x$ to $y$. That's it: a set $V$
and a family of sets over $V \times V$. Really, for our purposes, graphs
by themselves are not very interesting: their utility comes in
constructing new _categories_.

```agda
record Graph o ℓ : Type (lsuc o ⊔ lsuc ℓ) where
  field
    vert : Set o
    edge : ∣ vert ∣ → ∣ vert ∣ → Set ℓ
```

Given a graph $G$, we construct a [[strict category]] $\rm{Path}(G)$ in
the following manner:

- The objects of $\rm{Path}(G)$ are the vertices of $G$
- The morphisms in $\rm{Path}(G)$ are given by _finite paths_ in $G$.
Finite paths are defined by the following indexed-inductive type

<!--
```agda
module _ {o ℓ} (G : Graph o ℓ) where
  private module G = Graph G
```
-->

```agda
  data Path-in : ∣ G.vert ∣ → ∣ G.vert ∣ → Type (o ⊔ ℓ) where
    nil  : ∀ {a} → Path-in a a
    cons : ∀ {a b c} → ∣ G.edge a b ∣ → Path-in b c → Path-in a c
```

That is: a path is either empty, in which case it starts and ends at
itself (these are the identity morphisms), or we can form a path from $a
\to c$ by starting with a path $b \to c$ and precomposing with an edge
$(a \to b) : G$. Much of the code below is dedicated to characterising
the identity types between paths. Indeed, to construct a category
$\rm{Path}(G)$, we must show that paths in $G$ form a set.

We have a couple of options here:

- We can _construct_ paths _by recursion_, on their length: Defining a
"path from $x$ to $y$ of length $n$" by recursion on $n$, and then
defining a path from $x$ to $y$ as being a pair $(n, xs)$ where $n :
\N$$ and $xs$ is a path of length $n$;

- We can _define_ paths _by induction_, as is done above.

The former approach makes it easy to show that paths form a set: we can
directly construct the _set_ of paths, by recursion, then project the
underlying type if necessary. But working with these paths is very
inconvenient, since we have to deal with explicit identities between the
endpoints. The latter approach makes defining functions on paths easy,
but showing that they are a set is fairly involved. Let's see how to do
it.

The first thing we'll need is a predicate expressing that a path $xs : x
\to y$ really encodes the empty path, and we have an identity of
vertices $x \equiv y$. We can do this by recursion: If $xs$ is nil, then
we can take this to be the unit type, otherwise it's the bottom type.

```agda
  is-nil : ∀ {a b} → Path-in a b → Type (o ⊔ ℓ)
  is-nil nil        = Lift _ ⊤
  is-nil (cons _ _) = Lift _ ⊥
```

We'd like to define a relation $\rm{Code}(xs, ys)$, standing for an
identification of paths $xs \equiv ys$. But observe what happens in the
case where we've built up a path $a \to c$ by adding an edge: We know
that the edges start at $a$, and the inner paths end at $c$, but the
inner vertex may vary!

We'll need to package an identification $p : b \equiv b'$ in the
relation for $\rm{cons}$, and so, we'll have to encode for a path $xs
\equiv ys$ _over_ some identification of their start points. That's why
we have `path-codep`{.Agda} and not "path-code". A value in
$\rm{Codep}_b(xs, ys)$ codes for a path $xs \equiv ys$ over $b$.

```agda
  path-codep
    : ∀ (a : I → ∣ G.vert ∣) {c}
    → Path-in (a i0) c
    → Path-in (a i1) c
    → Type (o ⊔ ℓ)
```

Note that in the case where $xs = \rm{nil}$, Agda refines $b$ to be
definitionally $a$, and we can no longer match on the right-hand-side
path $ys$. That's where the `is-nil`{.Agda} predicate comes in: We say
that $ys$ is equal to $\rm{nil}$ if `is-nil`{.Agda} $ys$ holds. Of
course, a `cons`{.Agda} and a `nil`{.Agda} can never be equal.

```agda
  path-codep a nil ys = is-nil ys
  path-codep a (cons x xs) nil = Lift _ ⊥
```

The recursive case constructs an identification of `cons`{.Agda} cells
as a triple consisting of an identification between their intermediate
vertices, and over that data, an identification between the added edges,
and a code for an identification between the tails.

```agda
  path-codep a {c} (cons {b = b} x xs) (cons {b = b'} y ys) =
    Σ[ bs ∈ (b ≡ b') ]
      (PathP (λ i → ∣ G.edge (a i) (bs i) ∣) x y × path-codep (λ i → bs i) xs ys)
```

By recursion on the paths and the code for an equality, we can show that
if we have a code for an identification, we can indeed compute an
identification. The most involved case is actually when the lists are
empty, in which case we must show that `is-nil(xs)`{.Agda
ident=is-nil}^[for $xs : a \to b$ an arbitrary path] implies that $xs
\equiv \rm{nil}$, but it must be over an arbitrary identification
$p$^[which we know is a loop $a = a$]. Fortunately, vertices in a graph
$G$ live in a set, so $p$ is reflexivity.

```agda
  path-encode
    : ∀ (a : I → ∣ G.vert ∣) {c} xs ys
    → path-codep a xs ys
    → PathP (λ i → Path-in (a i) c) xs ys
  path-encode a (cons x xs) (cons y ys) (p , q , r) i =
    cons {a = a i} {b = p i} (q i) $ path-encode (λ i → p i) xs ys r i
  path-encode a nil ys p = lemma (λ i → a (~ i)) ys p where
    lemma : ∀ {a b} (p : a ≡ b) (q : Path-in a b)
          → is-nil q → PathP (λ i → Path-in (p (~ i)) b) nil q
    lemma {a = a} p nil (lift lower) = to-pathp $
      subst (λ e → Path-in e a) (sym p) nil ≡⟨ (λ i → subst (λ e → Path-in e a) (G.vert .is-tr a a (sym p) refl i) nil) ⟩
      subst (λ e → Path-in e a) refl nil    ≡⟨ transport-refl _ ⟩
      nil                                   ∎
    lemma _ (cons x p) ()
```

The next step is to show that codes for identifications between paths
live in a proposition; But this is immediate by their construction: in
every case, we can show that they are either literally a proposition
(the base case) or built out of propositions: this last case is
inductive.

```agda
  path-codep-is-prop
    : ∀ (a : I → ∣ G.vert ∣) {b}
    → (p : Path-in (a i0) b) (q : Path-in (a i1) b) → is-prop (path-codep a p q)
  path-codep-is-prop a nil xs x y = is-nil-is-prop xs x y where
    is-nil-is-prop : ∀ {a b} (xs : Path-in a b) → is-prop (is-nil xs)
    is-nil-is-prop nil x y = refl
  path-codep-is-prop a (cons h t) (cons h' t') (p , q , r) (p' , q' , r') =
    Σ-pathp (G.vert .is-tr _ _ _ _) $
    Σ-pathp
      (is-prop→pathp (λ i → PathP-is-hlevel' 1 (G.edge _ _ .is-tr) _ _) q q')
      (is-prop→pathp
        (λ i → path-codep-is-prop (λ j → G.vert .is-tr _ _ p p' i j) t t')
        r r')
```

And finally, by proving that there is a code for the reflexivity path,
we can show that we have an [[identity system]] in the type of paths from
$a$ to $b$ given by their codes. Since these codes are propositions, and
identity systems give a characterisation of a type's identity types, we
conclude that paths between a pair of vertices live in a set!

```agda
  path-codep-refl : ∀ {a b} (p : Path-in a b) → path-codep (λ i → a) p p
  path-codep-refl nil = lift tt
  path-codep-refl (cons x p) = refl , refl , path-codep-refl p

  path-identity-system
    : ∀ {a b}
    → is-identity-system {A = Path-in a b} (path-codep (λ i → a)) path-codep-refl
  path-identity-system = set-identity-system
    (path-codep-is-prop λ i → _)
    (path-encode _ _ _)

  path-is-set : ∀ {a b} → is-set (Path-in a b)
  path-is-set {a = a} = identity-system→hlevel 1 path-identity-system $
    path-codep-is-prop λ i → a
```

<!--
```agda
  path-decode
    : ∀ {a b} {xs ys : Path-in a b}
    → xs ≡ ys
    → path-codep (λ _ → a) xs ys
  path-decode = Equiv.from (identity-system-gives-path path-identity-system)
```
-->

## The path category

By comparison, constructing the actual precategory of paths is almost
trivial. The composition operation, concatenation, is defined by
recursion over the left-hand-side path. This is definitionally unital on
the left.

```agda
  _++_ : ∀ {a b c} → Path-in a b → Path-in b c → Path-in a c
  nil ++ ys = ys
  cons x xs ++ ys = cons x (xs ++ ys)
```

Right unit and associativity are proven by induction.

```agda
  ++-idr : ∀ {a b} (xs : Path-in a b) → xs ++ nil ≡ xs
  ++-idr nil         = refl
  ++-idr (cons x xs) = ap (cons x) (++-idr xs)

  ++-assoc
    : ∀ {a b c d} (p : Path-in a b) (q : Path-in b c) (r : Path-in c d)
    → (p ++ q) ++ r ≡ p ++ (q ++ r)
  ++-assoc nil q r        = refl
  ++-assoc (cons x p) q r = ap (cons x) (++-assoc p q r)
```

And that's it! Note that we must compose paths backwards, since the type
of the concatenation operation and the type of morphism composition are
mismatched (they're reversed).

```agda
  open Precategory
  Path-category : Precategory o (o ⊔ ℓ)
  Path-category .Ob = ∣ G.vert ∣
  Path-category .Hom = Path-in
  Path-category .Hom-set _ _ = path-is-set
  Path-category .id = nil
  Path-category ._∘_ xs ys = ys ++ xs
  Path-category .idr f = refl
  Path-category .idl f = ++-idr f
  Path-category .assoc f g h = ++-assoc h g f
```

Moreover, free categories are always _[gaunt]_: they are automatically
strict and, as can be seen with a bit of work, univalent. Univalence
follows because any non-trivial isomorphism would have to arise as a
`cons`{.Agda}, but `cons`{.Agda} can never be `nil`{.Agda} --- which
would be required for a composition to equal the identity.

[gaunt]: Cat.Gaunt.html

While types prevent us from directly stating "if a map is invertible, it
is `nil`{.Agda}", we can nevertheless pass around some equalities to
make this induction acceptable.

```agda
  Path-category-is-category : is-category Path-category
  Path-category-is-category = r where
    module Pc = Cat.Reasoning Path-category

    rem₁ : ∀ {x y} (j : Pc.Isomorphism x y) → Σ (x ≡ y) λ p → PathP (λ i → Pc.Isomorphism x (p i)) Pc.id-iso j
    rem₁ {x = x} im = go im (im .Pc.to) refl (path-decode (im .Pc.invr)) where
      go : ∀ {y} (im : Pc.Isomorphism x y) (j' : Path-in x y) → j' ≡ im .Pc.to
         → path-codep (λ _ → x) (j' ++ im .Pc.from) nil
         → Σ (x ≡ y) λ p → PathP (λ i → Pc.Isomorphism x (p i)) Pc.id-iso im
      go im nil p q = refl , Pc.≅-pathp refl refl p

    r : is-category Path-category
    r .to-path i      = rem₁ i .fst
    r .to-path-over i = rem₁ i .snd

  Path-category-is-gaunt : is-gaunt Path-category
  Path-category-is-gaunt = record
    { has-category = Path-category-is-category
    ; has-strict   = hlevel!
    }
```
