<!--
```agda
open import Cat.Functor.Adjoint
open import Cat.Diagram.Sieve
open import Cat.Site.Base
open import Cat.Prelude

import Cat.Functor.Reasoning.Presheaf as Psh
```
-->

```agda
module Cat.Site.Sheafification where
```

# Sheafification {defines="sheafification"}

::: source
The higher-inductive construction of sheafification presented in this
module is originally due to [Matthias Hutzler], in code that was
[contributed to the `cubical` library][cubical]. The `cubical` library
is distributed under the terms of the MIT license, [available here].

[Matthias Hutzler]: https://github.com/MatthiasHu
[cubical]: https://github.com/agda/cubical/tree/c26160bec3e8edf3d83597add765a01cc0bf982b/Cubical/Categories/Site/Sheafification
[available here]: https://github.com/agda/cubical/blob/c26160bec3e8edf3d83597add765a01cc0bf982b/LICENSE
:::

This module constructs the **sheafification** of a presheaf on $\cC$,
relative to an arbitrary [[coverage]] $J$ on $\cC$. Abstractly, this is
the [[left adjoint]] to the inclusion of sheaves on $(\cC, J)$ into
presheaves on $\cC$: in concrete terms, this means that, given a
presheaf $A : \psh(\cC)$, we construct a $J$-sheaf $A^+$ and a map $A
\to A^+$ which is universal among maps from $A$ to sheaves.

Unlike traditional constructions in the literature (e.g. those found in
[@Elephant, C2.2.6; @SIGL, chap. V, 3.7; @Stacks, 7.10]), which
construct sheafifications by a two-step construction, working in cubical
type theory lets us construct sheafifications *all at once*, using a
higher inductive type. As usual when constructing left adjoints, this
boils down to writing down an inductive type with constructors standing
for all the "generators" and "relations" that the object must satisfy,
then a bit of plumbing to establish the universal property in
categorical terms.

<!--
```agda
module Sheafification {o ℓ ℓc} {C : Precategory o ℓ} (J : Coverage C ℓc) {ℓs} (A : Functor (C ^op) (Sets ℓs)) where
  open Precategory C
  open Functor

  private
    module A = Functor A
    variable
      U V W : ⌞ C ⌟
      f g h : Hom U V

  -- The constructors 'glue' and 'glues' are why we define pre.Parts and
  -- pre.is-patch for "non-functors" (freestanding actions).
  --
  -- Ideally we would like to define Sheafify and Sheafify₀ by mutual
  -- recursion so we could instead say Patch Sheafify (J .cover c) but
  -- this angers both the termination and the positivity checker (and
  -- occasionally the scope checker).
```
-->

While this construction might not be familiar to working mathematicians,
we will see by, investigating each constructor in turn, that there is a
very natural set of "generators" and "relations" that present the
sheafification. Let us start with the generators: how can you construct
an element of $A^+(U)$?

First, $A^+$ admits a (universal) natural transformation from $A$, so we
must have a constructor standing for that, namely `inc`{.Agda}. Second,
$A^+$ must be a functor, so given $x : A^+(U)$ and $f : \cC(V,U)$, we
have a constructor `map`{.Agda} standing for the restriction $A^+(f)(x)
: A^+(V)$. Finally, $A^+$ is a [[sheaf]], so given any $J$-covering
sieve $s \in J(U)$, we can `glue`{.Agda} together a [[patch]] with
respect to $s$, living in $A^+(U)$.

```agda
  data Sheafify₀ : ⌞ C ⌟ → Type (o ⊔ ℓ ⊔ ℓs ⊔ ℓc) where
    inc : A ʻ U → Sheafify₀ U

    map : (f : Hom U V) → Sheafify₀ V → Sheafify₀ U

    glue
      : (c : J .covers U) (p : pre.Parts C map (J .cover c))
      → (g : pre.is-patch C map (J .cover c) p)
      → Sheafify₀ U
```

Then, we come to the relations, which are defined as *path*
constructors. First, we have constructors assuring that `map`{.Agda} is
functorial, and that `inc`{.Agda} is a natural transformation:

```agda
    map-id : ∀ x → map {U = U} id x ≡ x
    map-∘  : ∀ x → map (g ∘ f) x ≡ map f (map g x)

    inc-natural : (x : A ʻ U) → inc (A ⟪ f ⟫ x) ≡ map f (inc x)
```

To ensure that $A^+$ is a sheaf, we have two constructors: one states
that $A^+$ is [[separated|separated presheaf]] for any $J$-covering
sieve, and one states that the point obtained by `glue`{.Agda} really is
a section of the given patch.

```agda
    sep
      : ∀ {x y : Sheafify₀ U} (c : J .covers U)
      → (l : ∀ {V} (f : Hom V U) (hf : f ∈ J .cover c) → map f x ≡ map f y)
      → x ≡ y

    glues
      : (c : J .covers U) (p : pre.Parts C map (J .cover c))
      → (g : pre.is-patch C map (J .cover c) p)
      → pre.is-section C map (J .cover c) (glue c p g) p
```

Finally, we must tame all these generators for equality, by truncating
$A^+(U)$ to a [[set]].

```agda
    squash : is-set (Sheafify₀ U)
```

By distributing the data above, we see that $A^+$ is indeed a functor
(`Sheafify`{.Agda}), that it is separated, and that it is a sheaf.

```agda
  Sheafify : Functor (C ^op) (Sets (o ⊔ ℓ ⊔ ℓs ⊔ ℓc))
  Sheafify .F₀ x .∣_∣ = Sheafify₀ x
  Sheafify .F₀ x .is-tr = squash
  Sheafify .F₁ = map
  Sheafify .F-id    = funext map-id
  Sheafify .F-∘ f g = funext map-∘

  Sheafify-is-sep : is-separated J Sheafify
  Sheafify-is-sep c = sep c

  Sheafify-is-sheaf : is-sheaf J Sheafify
  Sheafify-is-sheaf = from-is-separated Sheafify-is-sep λ c s → record
    { part  = glue c (s .part) (s .patch)
    ; patch = glues c (s .part) (s .patch)
    }
```

## An induction principle

It remains to prove the universal property of $A^+$. Showing existence
of the natural transformation $A^+$ is easy, and showing that we can
factors maps $A \to B$ through $A^+$ when $B$ is a sheaf is similarly
uncomplicated. However, showing *uniqueness* of this factorisation is
slightly more complicated: we will need an *induction principle* for
$A^+$ to tackle this problem in a sensible way.

Every higher-inductive type has a [mechanically derivable] eliminator
into [[propositions]], which lets us get a section of a proposition $P$
given only its values at the point constructor. But sheafifications have
three point constructors: `inc`{.Agda}, `map`{.Agda}, and `glue`{.Agda}.
Showing a proposition is preserved by `map`{.Agda} feels redundant,
since functoriality feels like it should be automatic, and having to
handle the `glue`{.Agda} constructor feels unnatural.

[mechanically derivable]: 1Lab.Reflection.Induction.html

Hutzler shows us how to give a more natural elimination principle, which
furthermore handles `map`{.Agda} automatically. We will assume that we
have a family of [[propositions]] $P$, with sections over `inc`{.Agda}:

```agda
  Sheafify-elim-prop
    : ∀ {ℓp} (P : ∀ {U} → Sheafify₀ U → Type ℓp)
    → (pprop : ∀ {U} (x : Sheafify₀ U) → is-prop (P x))
    → (pinc : ∀ {U : ⌞ C ⌟} (x : A ʻ U) → P (inc x))
```

Instead of asking for $P$ over `glue`{.Agda}, we will ask instead that
$P$ be *local* for any $J$-covering sieve. Explicitly, this means that
we need to show $P(x)$, for $x : A^+(U)$ and a $J$-covering sieve $s$;
but we're allowed to assume that $P$ has already been shown for any
restriction $A^+(f)(x)$, as long as $f \in s$.

```agda
    → (plocal
        : ∀ {U : ⌞ C ⌟} (c : J .covers U) (x : Sheafify₀ U)
        → (∀ {V} (f : Hom V U) (hf : f ∈ J .cover c) → P (map f x)) → P x)
    → ∀ {U} (x : Sheafify₀ U) → P x
```

The key idea is to strengthen $P(x)$ to the proposition "$P$ holds at
every restriction of $x$"; we will call this stronger proposition $P'$.
Since $x$ is its own restriction along the identity, it is clear that
$P'(x)$ implies $P(x)$; it is also automatic that $P'$ is a family of propositions as well.

```agda
  Sheafify-elim-prop {ℓp} P pprop pinc plocal x = unp' (go x) where opaque
    P' : ∀ {U} (x : Sheafify₀ U) → Type (o ⊔ ℓ ⊔ ℓp)
    P' {U} x = ∀ {V} (f : Hom V U) → P (map f x)

    unp' : ∀ {U} {x : Sheafify₀ U} → P' x → P x
    unp' p' = subst P (map-id _) (p' id)

    p'prp : ∀ {U} (x : Sheafify₀ U) → is-prop (P' x)
    p'prp x = Π-is-hlevel' 1 λ V → Π-is-hlevel 1 λ f → pprop (map f x)
```

We now turn to showing $P'$ over every point constructor. First, it is
preserved by `map`{.Agda}, by functoriality: in a bit more detail,
suppose we have $x : A^+(V)$, $f : \cC(U, V)$, and $P'(x)$; we want to
show $P'(A^+(f)(x))$. Unfolding the definition of $P'$, this means that
we must show $P(A^+(g)(A^+(f)(x)))$, for any $g : \cC(W, V)$; but our
assumption means that we have $P(A^+(h)(x))$ for any $h : \cC(-, V)$.
Taking $h = fg$ gives $P(A^+(fg)(x))$, which is equal to our goal by
functoriality.

```agda
    p'map : ∀ {U V : ⌞ C ⌟} (f : Hom U V) (x : Sheafify₀ V) → P' x → P' (map f x)
    p'map f x p g = subst P (map-∘ _) (p (f ∘ g))
```

Similarly, we can show $P'(x)$ for the inclusion of an $x : A(U)$ at
every restriction, by naturality of `inc`{.Agda}.

```agda
    p'inc : ∀ {U : ⌞ C ⌟} (x : A ʻ U) → P' (inc x)
    p'inc x {V} f = subst P (inc-natural x) (pinc (A ⟪ f ⟫ x))
```

Finally, we must show that $P'$ preserves the `glue`{.Agda} constructor.
This is a bit more involved: suppose we have a $J$-covering sieve $s$ on
$U$, and a patch $p$ over $s$. For our induction hypothesis, we assume
$P'(p(f))$ for any $f \in s$. We want to show $P(A^+(f)(\operatorname{glue} p))$, given any $f : \cC(U, V)$.

```agda
    p'glue
      : ∀ {U : ⌞ C ⌟} (c : J .covers U) (p : pre.Parts C map (J .cover c))
      → (g : pre.is-patch C map (J .cover c) p)
      → (∀ {V} (f : Hom V U) (hf : f ∈ J .cover c) → P' (p f hf))
      → P' (glue c p g)
```

We will use the assumption that $P$ is local, at the pullback sieve
$f^*(s)$, which is $J$-covering since $J$ is a site: to show
$P(A^+(f)(\operatorname{glue} p))$, it will suffice to show this at
every restriction along $g \in f^*(s)$. Since $\operatorname{glue} p$ is
a section of $p$, it becomes equal to $p(fg)$ after restricting along
such a $g$. We have $P(p(fg))$ by assumption, and
$P(A^+(fg)(\operatorname{glue} p))$ by the preceding observation, so we
can finish by functoriality. This is a slightly tricky argument, so the
formalisation may actually be easier to read:

```agda
    p'glue c p compat loc f = ∥-∥-out (pprop _) do
      (c' , sub) ← J .stable c f
      pure $ plocal c' (map f (glue c p compat)) λ g hg →
        let
          it : P (map id (p (f ∘ g) (sub g hg)))
          it = loc (f ∘ g) (sub g hg) id
          q = map id (p (f ∘ g) _)            ≡⟨ map-id _ ⟩
              p (f ∘ g) _                     ≡˘⟨ glues c p compat (f ∘ g) (sub g hg) ⟩
              map (f ∘ g) (glue c p compat)   ≡⟨ map-∘ _ ⟩
              map g (map f (glue c p compat)) ∎
        in subst P q it
```

<!--
```agda
    go : ∀ {U} (x : Sheafify₀ U) → P' x
    go (map f x) = p'map f x (go x)
    go (inc x)   = p'inc x
    go (glue c p g) = p'glue c p g λ f hf → go (p f hf)
    go (inc-natural {f = f} x i) = is-prop→pathp (λ i → p'prp (inc-natural x i)) (p'inc (A.₁ f x)) (p'map f (inc x) (p'inc x)) i
    go (sep {x = x} {y = y} c l i) = is-prop→pathp (λ i → p'prp (sep c l i)) (go x) (go y) i
    go (map-id x i) = is-prop→pathp (λ i → p'prp (map-id x i)) (p'map id x (go x)) (go x) i
    go (map-∘ {g = g} {f = f} x i) = is-prop→pathp (λ i → p'prp (map-∘ x i)) (p'map (g ∘ f) x (go x)) (p'map f (map g x) (p'map g x (go x))) i
    go (glues c p g f hf i) = is-prop→pathp (λ i → p'prp (glues c p g f hf i)) (p'map f (glue c p g) (p'glue c p g λ g hg → go (p g hg))) (go (p f hf)) i
    go (squash x y p q i j) = is-prop→squarep (λ i j → p'prp (squash x y p q i j)) (λ i → go x) (λ i → go (p i)) (λ i → go (q i)) (λ i → go y) i j
```
-->

## The universal property

<!--
```agda
module Small {ℓ} {C : Precategory ℓ ℓ} (J : Coverage C ℓ)  where
  open Sheafification J

  open _=>_

  private variable A : Functor (C ^op) (Sets ℓ)
```
-->

Using the induction principle above, we may show the categorical
universal property of $A^+$. However, at this stage, we must pay
attention to the universe levels involved. Let us recap:

- A site, as a category $\cC$ with a coverage $J$, is parametrised over
  three universe levels: one for the type of objects of $\cC$, one for
  $\cC$'s $\hom$-sets, and one for the collection of $J$-covers.
  Finally, we can consider presheaves on $\cC$ valued in a completely
  arbitrary universe.

  The sheafification construction is fully general: the type $A^+(U)$
  simply lives in the least universe larger than all those that
  parametrise $\cC$, $J$ and $A$.

- The functor category $[\cC\op, \Sets_\ell]$ is parametrised by a
  universe level $\ell$. Among other things, this means that we can only
  *really* consider natural transformations between presheaves valued in
  the same universe level.

  Moreover, to get a [[Cartesian closed]] category of presheaves, $\cC$
  must be small --- its objects and $\hom$s must live in the same
  universe --- and they must be valued in that same universe level.

In practice, this means that, while the construction of $A^+(U)$ is
parametrised over four universe levels, we only obtain a nice universal
property if $\cC$ is some $\ell$-small category, equipped with an
$\ell$-small coverage, and we are talking about presheaves valued in the
category $\Sets_\ell$ of $\ell$-small sets. As a result, the
sheafification functor *qua* left adjoint is only parametrised over this
one universe level.

Returning to the construction, the universal natural transformation is
easy to define:

```agda
  unit : A => Sheafify A
  unit .η _ = inc
  unit .is-natural x y f = funext inc-natural
```

And, if $B$ is a $J$-sheaf, extending a map $\eta : A \to B$ to a map
$\eta' : A^+ \to B$ is similarly straightforward. At each construction
of $A^+(U)$, we have a corresponding operation valued in $B(U)$,
deferring to $\eta$ for the inclusion of points from $A(U)$. Similarly,
the path constructors are all handled by the corresponding laws in $B$.

```agda
  univ : (B : Functor (C ^op) (Sets ℓ)) → is-sheaf J B → A => B → Sheafify A => B
  univ {A = A} G shf eta = nt where
    private module G = Psh G
    go : ∀ U → Sheafify₀ A U → G ʻ U
    go U (inc x)   = eta .η U x
    go U (map f x) = G ⟪ f ⟫ (go _ x)
    go U (glue c p g) =
      shf .part c record { patch = λ f hf h hhf i → go _ (g f hf h hhf i) }
```

<details>
<summary>We will leave the laws in this little `<details>`{.html} block,
since they're a tad uglier than the cases above. Note also that
naturality of $\eta'$ is a definitional equality.</summary>

```agda
    go U (map-id x i) = G.F-id {x = go _ x} i
    go U (map-∘ {g = g} {f = f} x i) = G.F-∘ f g {x = go _ x} i
    go U (inc-natural {f = f} x i) = eta .is-natural _ U f i x
    go U (sep {x = x} {y = y} c l i) = shf .separate c {go _ x} {go _ y} (λ f hf i → go _ (l f hf i)) i
    go U (glues c p g f hf i) = shf .patch c record { patch = λ f hf h hhf i → go _ (g f hf h hhf i) } f hf i
    go U (squash x y p q i j) = G.₀ U .is-tr (go U x) (go U y) (λ i → go U (p i)) (λ i → go U (q i)) i j

    nt : Sheafify A => G
    nt .η = go
    nt .is-natural x y f = refl
```

</details>

Finally, we can show that $\eta'$ is the unique map which extends
$\eta$. This is very straightforward with our induction principle for
$A^+$, and the assumption that $B$ is a $J$-sheaf implies that equality
in $B(U)$ is $J$-local.

```agda
  unique
    : (G : Functor (C ^op) (Sets ℓ)) (shf : is-sheaf J G) (eta : A => G) (eps : Sheafify A => G)
    → (∀ U (x : A ʻ U) → eps .η U (inc x) ≡ eta .η U x)
    → univ G shf eta ≡ eps
  unique {A = A} G shf eta eps comm = ext λ i → Sheafify-elim-prop A
    (λ {v} x → univ G shf eta .η v x ≡ eps .η v x)
    (λ {U} x → hlevel 1)
    (λ x → sym (comm _ x))
    (λ c x l → is-sheaf.separate shf c (λ f hf → l f hf ∙ eps .is-natural _ _ _ # _))
```

<!--
```agda
  private module fo = Free-object

  make-free-sheaf : ∀ F → Free-object (forget-sheaf J ℓ) F
  make-free-sheaf F .fo.free = Sheafify F , Sheafify-is-sheaf F
  make-free-sheaf F .fo.unit = unit
  make-free-sheaf F .fo.fold {G , shf} = univ G shf
  make-free-sheaf F .fo.commute = trivial!
  make-free-sheaf F .fo.unique {G , shf} _ p = sym $
    unique G shf _ _ λ U x → p ηₚ _ $ₚ _
```
-->
