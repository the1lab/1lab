<!--
```agda
open import Cat.Instances.Functor
open import Cat.Diagram.Sieve
open import Cat.Prelude hiding (glue)

import Cat.Functor.Reasoning.Presheaf as Psh
import Cat.Reasoning as Cat
```
-->

```agda
module Cat.Site.Base where
```

<!--
```agda
private variable
  o ℓ ℓc ℓs : Level
  C : Precategory o ℓ
```
-->

# Sites and sheaves

**Sheaf theory** is a particular formalisation of the idea that *global*
structure $A(U)$ on a complicated object $U$ is often best studied at
its *restrictions* to simpler parts $V_i$ which *glue* to recover $U$.
It's particularly general, in the sense that the objects $U$ can belong
to an arbitrary category $\cC$, as long as we equip $\cC$ with structure
(called a **coverage**) determining what we mean by *glue together* ---
and as long as our global structure $A(U)$ is fine living at the level
of [[set]]s.

::: source
Most of our material on sheaf theory is adapted from the Elephant
[-@Elephant], specifically chapter C2.
:::

To make these ideas concrete, we will fix a category $\cC$ of objects we
want to study, and we will denote its objects by letters like $U\!$,
$V\!$, and $W\!$. The structures we will be interested in will all take
the form of *presheaves* on $\cC$ --- functors into the category
$\Sets$. If we have any family of maps $(h_i : U_i \to U)_i$, and an
element $s : A(U)$, then $A's$ functorial action ensures that we can
restrict $s$ along the $h_i$ to obtain elements $s_i : A(U_i)$.

A representative example is when $\cC$ is the [[frame]] $\Omega(L)$
underlying some locale $L$, and the elements $U_i$ are such that $U =
\bigvee_i U_i$. This setup has the particular *geometric* interpretation
of expressing $U$ as a union of smaller parts. Extending this intuition,
we would consider our original $s : A(U)$ to be the *global*
information, and the restrictions $s_i : A(U_i)$ to be information
*local* to a given sub-part of the whole $U$.

So far, we have said nothing new: this is simply functoriality. The
interesting question is going *the other way*: if we have the local
information $s_i : A(U_i)$, can we glue them together to get the global
information $s : A(U)$? We can't *always*: this might be a failure of
the functor[^failure], or of the $s_i$. While it might be a bit
disheartening that there are notions of "information" which can not be
put together locally, these failures tell us that we have a fruitful
concept at hand.

[^failure]:
    For a functor that is not a sheaf, consider the category

    ~~~{.quiver}
    \[\begin{tikzcd}[ampersand replacement=\&]
      \& {\{0,1\}} \\
      {\{0\}} \&\& {\{1\}} \\
      \& {\{\}}
      \arrow[from=3-2, to=2-1]
      \arrow[from=3-2, to=2-3]
      \arrow[from=2-1, to=1-2]
      \arrow[from=2-3, to=1-2]
    \end{tikzcd}\]
    ~~~

    and define a functor $A(-)$ by sending $\{\}$ to the unit set, both
    singleton sets to $\bZ$, and the two-element set to $\bZ \times \bZ
    \times \bZ$; the restriction mappings are the projections onto the
    first two factors.

    We will later see that, were $A$ a sheaf, the elements of
    $A(\{0,1\})$ would have their equality determined by their
    restrictions to $A(\{0\})$ and $A(\{1\})$ --- but by this measure,
    $(0, 0, 0)$ and $(0, 0, 1)$ would have to be equal.

First, assuming that our $s_i : A(U_i)$ are all restrictions of some $s
: A(U)$, we should investigate the properties it *must* have: these will
tell us what properties we should impose on local data $t_i : A(V_i)$ to
ensure it has a *chance* of gluing to a $t : A(V)$. The key property is,
once again, functoriality --- but it also has a *geometric*
interpretation. Suppose we have two objects $U_i$ and $U_j$ drawn from
our family, and some arbitrary third object $V$, and they fit into a
commutative diagram like

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  \& V \\
  {U_i} \&\& {U_j} \\
  \& {U\text{.}}
  \arrow["{h_i}"', from=2-1, to=3-2]
  \arrow["{h_j}", from=2-3, to=3-2]
  \arrow["f"', from=1-2, to=2-1]
  \arrow["g", from=1-2, to=2-3]
\end{tikzcd}\]
~~~

If we are still thinking about $\cC = \Omega(L)$, then $V$ could simply
be the intersection $U_i \cap U_j$, and the diagram commutes
automatically. In any case, we have two ways of restricting $s : A(U)$
to the intersection $V$, namely $A(f)(s_i)$ and $A(g)(s_j)$. By
functoriality, we have

$$
A(f)(s_i) = A(fh_i)(s) = A(gh_j)(s) = A(g)(s_j)\text{,}
$$

so that, if our "local" data comes from restricting "global" data, the
local restrictions automatically *agree on intersections*. We thus have
defined what it means to have *local data* with respect to a family of
morphisms (which we think of as expressing their common codomain as
being "glued together"), and what it means for that data to *glue* to
give local data.

We could carry on and define sheaves from here, but we will make one
final simplifying assumption: Instead of considering *families* of
morphisms with common codomain, we will consider [[sieves]] in $\cC$.
This lets us simplify the notion of compatibility: we now have values
$s(fh_i)$ of $s$ at arbitrary composites of the $h_i$, so that it
suffices to demand $A(f)(s(h_i)) = s(fh_i)$.

## Terminology for local data {defines="patch"}

<!--
```agda
-- Defining these notions for "non-functors" first will let us avoid
-- angering the positivity checker when defining sheafifications, see
-- that module for more details.
module pre {o ℓ ℓs} (C : Precategory o ℓ) {A₀ : ⌞ C ⌟ → Type ℓs} (A₁ : ∀ {U V} → C .Precategory.Hom U V → A₀ V → A₀ U) where
  open Precategory C
```
-->

To formalise the notion of sheaf, we will need to introduce names for
the ideas we've sketched out so far. First, if we are given a sieve $f_i
: U_i \to U$, we will refer to a family of elements $s(f_i) : A(U_i)$ as
a family of **parts**. If these parts satisfy the compatibility
condition defined above, relative to the sieve $f_i$, we will say they
are a **patch**. The geometric intuition is key here: the $s(f_i)$ are
to be the literal *parts* of some hypothetical $s : A(U)$, and they're a
patch if they agree on the "intersections" $U_i \ot V \to U_j$.

```agda
  Parts : ∀ {U} (T : Sieve C U) → Type _
  Parts {U} T = ∀ {V} (f : Hom V U) (hf : f ∈ T) → A₀ V

  is-patch : ∀ {U} (T : Sieve C U) (p : Parts T) → Type _
  is-patch {U} T part =
    ∀ {V W} (f : Hom V U) (hf : f ∈ T) (g : Hom W V) (hgf : f ∘ g ∈ T)
    → A₁ g (part f hf) ≡ part (f ∘ g) hgf
```

Finally, if we have a family $s(f_i) : A(U_i)$ of parts, then we say
that an element $s : A(U)$ is a **section** of these parts if its
restriction along each $f_i$ agrees with the part $s(f_i)$:

```agda
  is-section : ∀ {U} (T : Sieve C U) → A₀ U → Parts T → Type _
  is-section {U = U} T s p =
    ∀ {V} (f : Hom V U) (hf : f ∈ T)
    → A₁ f s ≡ p f hf
```

<!--
```agda
module _ {o ℓ ℓs} {C : Precategory o ℓ} (A : Functor (C ^op) (Sets ℓs)) where
  open Precategory C
  private module A = Psh A
  open pre C A.₁ hiding (is-section)
```
-->

We will most often consider parts-which-are-patches, so we introduce a
record type to bundle them; similarly, we will consider
elements-which-are-sections, so they also get a record type.

```agda
  record Patch {U} (T : Sieve C U) : Type (o ⊔ ℓ ⊔ ℓs) where
    no-eta-equality
    field
      part  : Parts T
      patch : is-patch T part
```

<!--
```agda
    abstract
      app : ∀ {V} {f g : Hom V U} {hf hg} → f ≡ g → part f hf ≡ part g hg
      app p = ap₂ part p prop!

      compatible
        : ∀ {V W X} {i : Hom W U} {j : Hom X U} (g : Hom V W) (h : Hom V X)
        → {is : i ∈ T} {js : j ∈ T}
        → i ∘ g ≡ j ∘ h
        → A ⟪ g ⟫ part i is ≡ A ⟪ h ⟫ part j js
      compatible {i = i} {j} g h {is} {js} p =
        A ⟪ g ⟫ part i is ≡⟨ patch i _ g (T .closed is g) ⟩
        part (i ∘ g) _    ≡⟨ app p ⟩
        part (j ∘ h) _    ≡⟨ sym (patch j _ h (T .closed js h)) ⟩
        A ⟪ h ⟫ part j js ∎

  open Patch

  is-section : ∀ {U} {T : Sieve C U} → A ʻ U → Patch T → Type _
  is-section {T = T} p x = pre.is-section C A.₁ T p (x .part)
```
-->

```agda
  record Section {U} {T : Sieve C U} (p : Patch T) : Type (o ⊔ ℓ ⊔ ℓs) where
    no-eta-equality
    field
      {part} : A ʻ U
      patch  : is-section part p
```

<!--
```agda
module _ {o ℓ ℓs} {C : Precategory o ℓ} {A : Functor (C ^op) (Sets ℓs)} where
  open Cat C
  open Section
  open Patch
  private module A = Psh A
  open pre C A.₁ hiding (is-section) public

  instance
    Extensional-Patch
      : ∀ {U ℓr} {S : Sieve C U} ⦃ _ : Extensional (Parts S) ℓr ⦄
      → Extensional (Patch A S) ℓr
    Extensional-Patch ⦃ e ⦄ .Pathᵉ x y = e .Pathᵉ (x .part) (y .part)
    Extensional-Patch ⦃ e ⦄ .reflᵉ x = e .reflᵉ (x .part)
    Extensional-Patch ⦃ e ⦄ .idsᵉ .to-path p i .part = e .idsᵉ .to-path p i
    Extensional-Patch ⦃ e ⦄ .idsᵉ .to-path {x} {y} p i .patch {W = W} f hf g hgf =
      is-prop→pathp (λ i → A.₀ W .is-tr (A.₁ g (e .idsᵉ .to-path p i _ hf)) (e .idsᵉ .to-path p i _ hgf))
        (x .patch f hf g hgf) (y .patch f hf g hgf) i
    Extensional-Patch ⦃ e ⦄ .idsᵉ .to-path-over p = is-prop→pathp (λ i → Pathᵉ-is-hlevel 1 e (hlevel 2)) _ _

    Extensional-Section
      : ∀ {U ℓr} {S : Sieve C U} {p : Patch A S} ⦃ _ : Extensional (A ʻ U) ℓr ⦄
      → Extensional (Section A p) ℓr
    Extensional-Section ⦃ e ⦄ .Pathᵉ x y = e .Pathᵉ (x .part) (y .part)
    Extensional-Section ⦃ e ⦄ .reflᵉ x = e .reflᵉ (x .part)
    Extensional-Section ⦃ e ⦄ .idsᵉ .to-path p i .part = e .idsᵉ .to-path p i
    Extensional-Section {p = p} ⦃ e ⦄ .idsᵉ .to-path {a} {b} q i .patch {V} f hf =
      is-prop→pathp (λ i → A.₀ V .is-tr (A.₁ f (e .idsᵉ .to-path q i)) (p .part f hf))
        (a .patch f hf) (b .patch f hf) i
    Extensional-Section ⦃ e ⦄ .idsᵉ .to-path-over p = is-prop→pathp (λ i → Pathᵉ-is-hlevel 1 e (hlevel 2)) _ _

  subset→patch
    : ∀ {U} {S S' : Sieve C U}
    → (∀ {V} (f : Hom V U) → f ∈ S' → f ∈ S)
    → Patch A S
    → Patch A S'
  subset→patch incl p .part f hf = p .part f (incl f hf)
  subset→patch incl p .patch f hf g hgf = p .patch f _ g _

  pullback-patch : ∀ {U V} {S : Sieve C U} (f : Hom V U) → Patch A S → Patch A (pullback f S)
  pullback-patch {S = S} f s .part g p = s .part (f ∘ g) p
  pullback-patch {S = S} f s .patch g h hfg hfgh =
      s .patch (f ∘ g) h hfg (S .closed h hfg)
    ∙ app s (pullr refl)

  open _=>_

  map-patch
    : ∀ {B : Functor (C ^op) (Sets ℓs)} {U} {S : Sieve C U} (eta : A => B)
    → Patch A S
    → Patch B S
  map-patch eta x .part f hf = eta .η _ (x .part f hf)
  map-patch eta x .patch f hf g hgf = sym (eta .is-natural _ _ _ $ₚ _) ∙ ap (eta .η _) (x .patch f hf g hgf)
```
-->

Finally, we will formalise the idea that any *global* information $s :
A(U)$ can be made into a bunch of *local* pieces by restricting
functorially.

```agda
  section→patch : ∀ {U} {T : Sieve C U} → A ʻ U → Patch A T
  section→patch x .part  f _ = A ⟪ f ⟫ x
  section→patch x .patch f hf g hgf = A.collapse refl

  section→section
    : ∀ {U} {T : Sieve C U} (u : A ʻ U)
    → Section A {T = T} (section→patch u)
  section→section u .part       = u
  section→section u .patch f hf = refl
```

## The notion of sheaf {defines="sheaf sheaves"}

Using our terminology above, we can very concisely define what it means
for a functor $A : \psh(\cC)$ to be a sheaf, at least with respect to a
sieve $T$ on $U$: any patch $p$ of $T$ has a unique section. Thinking
intuitively, satisfying the sheaf condition for a sieve $T$ means that
each $s : A(U)$ arises uniquely as the gluing of some patch $s(f_i) :
A(U_i)$.

<!--
```agda
module _ {o ℓ ℓs} {C : Precategory o ℓ} (A : Functor (C ^op) (Sets ℓs)) where
  open Precategory C
  open Section
  open Patch
```
-->

```agda
  is-sheaf₁ : ∀ {U} (T : Sieve C U) → Type _
  is-sheaf₁ T = (p : Patch A T) → is-contr (Section A p)
```

::: {.definition #separated-presheaf}
We will also need the notion of **separated presheaf**. These are
typically defined to be the presheaves which have *at most one* section
for each patch: the type of sections for each patch is a
[[proposition]], instead of being [[contractible]].

But from a type-theoretic perspective, it makes more sense to define
separated presheaves in the following "unfolded" form, which says that
that equality on $A(U)$ is a $T$-local property.
:::

```agda
  is-separated₁ : ∀ {U} (T : Sieve C U) → Type _
  is-separated₁ {U} T =
    ∀ {x y : A ʻ U}
    → (∀ {V} (f : Hom V U) (hf : f ∈ T) → A ⟪ f ⟫ x ≡ A ⟪ f ⟫ y)
    → x ≡ y
```

Note that every sheaf is indeed separated, even after this unfolding,
using the above mapping from elements to sections. The assumption of
"$T$-local equality" is exactly what we need to assure that $y$ is
*also* a section of the patch generated by restricting $x$.

```agda
  is-sheaf₁→is-separated₁ : ∀ {U} (T : Sieve C U) → is-sheaf₁ T → is-separated₁ T
  is-sheaf₁→is-separated₁ T sheaf {x} {y} lp = ap part $
    let
      sec₁ : Section A (section→patch x)
      sec₁ = section→section x

      sec₂ : Section A (section→patch x)
      sec₂ = record
        { part  = y
        ; patch = λ f hf →
          A ⟪ f ⟫ y ≡˘⟨ lp f hf ⟩
          A ⟪ f ⟫ x ∎
        }
    in is-contr→is-prop (sheaf (section→patch x)) sec₁ sec₂
```

<!--
```agda
  from-is-separated₁
    : ∀ {U} {T : Sieve C U}
    → is-separated₁ T
    → ∀ {p : Patch A T} (s : Section A p)
    → is-contr (Section A p)
  from-is-separated₁ sep sec .centre = sec
  from-is-separated₁ sep sec .paths x = ext $ sep λ f hf →
    sec .patch f hf ∙ sym (x .patch f hf)

  -- This is equal to `subst (is-sheaf₁ A)` but has better definitional
  -- behaviour for the relevant part.
  subst-is-sheaf₁ : ∀ {U} {T S : Sieve C U} (p : T ≡ S) → is-sheaf₁ T → is-sheaf₁ S
  subst-is-sheaf₁ {T = T} {S = S} p shf pa = done where
    pa' : Patch A T
    pa' .part f hf = pa .part f (subst (f ∈_) p hf)
    pa' .patch f hf g hgf = pa .patch f _ g _

    sec = shf pa'

    done : is-contr (Section A pa)
    done .centre .part = sec .centre .part
    done .centre .patch f hf = sec .centre .patch f (subst (f ∈_) (sym p) hf) ∙ app pa refl
    done .paths x = ext (ap part (sec .paths record { patch = λ f hf → x .patch f (subst (f ∈_) p hf) ∙ app pa refl }))
```
-->

# Sites, formally {defines="site coverage"}

Up until now, we have only been considering *single* sieves $f_i : U_i
\to U$ when defining parts, patches, sections and sheaves. But a given
category, even the opens of a locale, will generally have many
*distinct* sieves on $U$ which could equally well be taken to be
*decompositions of $U$*. We would like a sheaf "on $\cC$" to have the
local-to-global property for all of these decompositions, but we need to
impose *some* order to make sure that we end up with a well-behaved
*category of sheaves.*

We define a **coverage** $J$ on $\cC$ to consist of, for each $U : \cC$,
a family $J(U)$ of **covering sieves** on $U$. Translating this into
type theory, for each $U$, we have a type $J(U)$ of "$J$-covers of $U$",
and, for each $x : J(U)$, we have an associated sieve $J(x)$ on $U$.

```agda
record Coverage {o ℓ} (C : Precategory o ℓ) ℓc : Type (o ⊔ ℓ ⊔ lsuc ℓc) where
  no-eta-equality

  open Precategory C

  field
    covers : ⌞ C ⌟ → Type ℓc
    cover  : ∀ {U} → covers U → Sieve C U
```

The $J(U)$ must satisfy the following *stability* property: if $R :
J(U)$ is some covering sieve, and $f : V \to U$ is an arbitrary
morphism, then [[there merely exists|merely]] a covering sieve $S :
J(V)$ which *is contained in* the [[pullback sieve]] $f^*(R)$. The
quantifier complexity for this statement is famously befuddling, but
stating it in terms of sieves does simplify the formalisation:

```agda
    stable
      : ∀ {U V : ⌞ C ⌟} (R : covers U) (f : Hom V U)
      → ∃[ S ∈ covers V ] (∀ {W} (g : Hom W V) → g ∈ cover S → f ∘ g ∈ cover R)
```

Thinking back to the case of $\cC = \Omega(L)$, we can equip any frame
with [[a coverage|frames as sites]]. The stability condition, in that
case, reduces to showing that, if a family $U_i \mono U$ has all of $U$
as its union, then the family $(U_i \cap V) \mono (U \cap V)$ has $U
\cap V$ as *its* union.

<!--
```agda
open Coverage public

instance
  Funlike-Coverage : Funlike (Coverage C ℓc) ⌞ C ⌟ (λ _ → Type ℓc)
  Funlike-Coverage = record { _#_ = λ C U → C .covers U }

  Membership-Coverage : ∀ {U} → Membership (Coverage C ℓc) (Sieve C U) _
  Membership-Coverage = record { _∈_ = λ C S → fibre (C .cover) S }
```
-->

<!--
```agda
module _ {o ℓ ℓc ℓs} {C : Precategory o ℓ} (J : Coverage C ℓc) (A : Functor (C ^op) (Sets ℓs)) where
```
-->

Finally, we (re-)define separated presheaves and sheaves with respect to
a coverage $J$. For separated presheaves, we can simply reuse the
definition given above, demanding it for every $J$-covering sieve. But
for sheaves, formalisation concerns lead us to instead define an
"unpacked" record type:

```agda
  is-separated : Type _
  is-separated = ∀ {U : ⌞ C ⌟} (c : J # U) → is-separated₁ A (J .cover c)

  record is-sheaf : Type (o ⊔ ℓ ⊔ ℓs ⊔ ℓc) where
    no-eta-equality
    field
      part     : ∀ {U} (S : J .covers U) (p : Patch A (J .cover S)) → A ʻ U
      patch    : ∀ {U} (S : J .covers U) (p : Patch A (J .cover S)) → is-section A (part S p) p
      separate : is-separated
```

This splitting of the sheaf condition into an *operation* and *laws*
will help us in defining [[sheafifications]] later on. We can package
the first two fields as saying that each patch has a section:

```agda
    split : ∀ {U} {S : J .covers U} (p : Patch A (J .cover S)) → Section A p
    split p .Section.part  = part _ p
    split p .Section.patch = patch _ p

  open is-sheaf using (part ; patch ; separate) public
```

Note that, if a functor satisfies the sheaf condition for all
$J$-covering sieves, it's also a sheaf relative to quite a few other
sieves: these are the [[closure properties of sites]].

<!--
```agda
module _ {o ℓ ℓc ℓs} {C : Precategory o ℓ} {J : Coverage C ℓc} {A : Functor (C ^op) (Sets ℓs)} where
  from-is-separated
    : is-separated J A
    → (∀ {U} (c : J .covers U) (s : Patch A (J .cover c)) → Section A s)
    → is-sheaf J A
  from-is-separated sep split .part S p   = split S p .Section.part
  from-is-separated sep split .patch S p  = split S p .Section.patch
  from-is-separated sep split .separate S = sep S

  from-is-sheaf₁
    : (∀ {U} (c : J .covers U) → is-sheaf₁ A (J .cover c))
    → is-sheaf J A
  from-is-sheaf₁ shf .part S p = shf _ p .centre .Section.part
  from-is-sheaf₁ shf .patch S p = shf _ p .centre .Section.patch
  from-is-sheaf₁ shf .separate S = is-sheaf₁→is-separated₁ _ _ (shf _)

  to-is-sheaf₁ : is-sheaf J A → ∀ {U} (c : J .covers U) → is-sheaf₁ A (J .cover c)
  to-is-sheaf₁ shf c p = from-is-separated₁ _ (shf .separate c) (is-sheaf.split shf p)
```
-->

<!--
```agda
open Section public
open Patch public

module _ {o ℓ ℓc ℓp} {C : Precategory o ℓ} {J : Coverage C ℓc} {A : Functor (C ^op) (Sets ℓp)} where
  private unquoteDecl eqv = declare-record-iso eqv (quote is-sheaf)
  abstract instance
    H-Level-is-sheaf : ∀ {n} → H-Level (is-sheaf J A) (suc n)
    H-Level-is-sheaf = prop-instance $ retract→is-hlevel 1 from to ft (hlevel 1) where
      T : Type (o ⊔ ℓ ⊔ ℓc ⊔ ℓp)
      T = ∀ {U} (S : J .covers U) (p : Patch A (J .cover S)) → is-contr (Section A p)

      from : T → is-sheaf J A
      from x .part  S p  = x S p .centre .part
      from x .patch S p  = x S p .centre .patch
      from x .separate S = is-sheaf₁→is-separated₁ A _ (x S)

      to : is-sheaf J A → T
      to shf S p = from-is-separated₁ _ (shf .separate S) (is-sheaf.split shf p)

      ft : ∀ x → from (to x) ≡ x
      ft x = Iso.injective eqv (Σ-prop-path! refl)
```
-->

<!--
```agda
module _ {o ℓ ℓc} {C : Precategory o ℓ} (J : Coverage C ℓc) ℓs where
  open Precategory
  open Functor
```
-->

We will often refer to a category $\cC$ with a coverage $J$ as the
**site** $(\cC, J)$. The first notion we define relative to sites is the
category of *sheaves on a site*, $\Sh(\cC, J)$: the [[full subcategory]]
of the presheaves on $\cC$ which are $J$-sheaves. The nature of the
sheaf condition ensures that $\Sh(\cC, J)$ inherits most of
$\psh(\cC)$'s good categorical properties --- we refer to it as the
[[topos of sheaves]].

```agda
  Sheaf : Type _
  Sheaf = Σ[ p ∈ Functor (C ^op) (Sets ℓs) ] is-sheaf J p

  Sheaves : Precategory (o ⊔ ℓ ⊔ ℓc ⊔ lsuc ℓs) (o ⊔ ℓ ⊔ ℓs)
  Sheaves .Ob = Sheaf
  Sheaves .Hom (S , _) (T , _) = S => T
  Sheaves .Hom-set _ _ = hlevel 2
  Sheaves .id  = idnt
  Sheaves ._∘_ = _∘nt_
  Sheaves .idr   f     = trivial!
  Sheaves .idl   f     = trivial!
  Sheaves .assoc f g h = trivial!

  forget-sheaf : Functor Sheaves (PSh ℓs C)
  forget-sheaf .F₀ (S , _) = S
  forget-sheaf .F₁ f = f
  forget-sheaf .F-id = refl
  forget-sheaf .F-∘ f g = refl
```
