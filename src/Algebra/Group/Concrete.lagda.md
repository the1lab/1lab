<!--
```agda
open import 1Lab.Path.Reasoning

open import Algebra.Group.Cat.Base
open import Algebra.Group.Homotopy
open import Algebra.Group.Ab
open import Algebra.Group

open import Cat.Functor.Equivalence
open import Cat.Functor.Properties
open import Cat.Morphism
open import Cat.Prelude

open import Data.Int

open import Homotopy.Space.Delooping
open import Homotopy.Connectedness
open import Homotopy.Space.Circle
open import Homotopy.Conjugation

open is-group-hom
open Precategory
open Functor
```
-->

```agda
module Algebra.Group.Concrete where
```

<!--
```agda
private variable
  ℓ ℓ' : Level
```
-->

# Concrete groups {defines="concrete-group"}

In homotopy type theory, we can give an alternative definition of [[groups]]:
they are the [[pointed|pointed type]], [[connected]] [[groupoids]].
The idea is that those groupoids contain exactly the same information as their
[[fundamental group]].

Such groups are dubbed **concrete**, because they represent the groups of symmetries
of a given object (the base point); by opposition, "algebraic" `Group`{.Agda}s are
called **abstract**.

```agda
record ConcreteGroup ℓ : Type (lsuc ℓ) where
  no-eta-equality
  constructor concrete-group
  field
    B                : Type∙ ℓ
    has-is-connected : is-connected∙ B
    has-is-groupoid  : is-groupoid ⌞ B ⌟

  pt : ⌞ B ⌟
  pt = B .snd
```

Given a concrete group $G$, the underlying pointed type is denoted $\B{G}$, by analogy
with the [[delooping]] of an abstract group; note that, here, the delooping *is* the
chosen representation of $G$, so `B`{.Agda} is just a record field.
We write $\point{G}$ for the base point.

Concrete groups are pointed connected types, so they enjoy the following elimination
principle, which will be useful later:

```agda
  B-elim-contr : {P : ⌞ B ⌟ → Type ℓ'}
               → is-contr (P pt)
               → ∀ x → P x
  B-elim-contr {P = P} c = connected∙-elim-prop {P = P} has-is-connected
    (is-contr→is-prop c) (c .centre)
```

<!--
```agda
  instance
    H-Level-B : ∀ {n} → H-Level ⌞ B ⌟ (3 + n)
    H-Level-B = basic-instance 3 has-is-groupoid

open ConcreteGroup

instance
  Underlying-ConcreteGroup : Underlying (ConcreteGroup ℓ)
  Underlying-ConcreteGroup {ℓ} .Underlying.ℓ-underlying = ℓ
  Underlying-ConcreteGroup .⌞_⌟ G = ⌞ B G ⌟

ConcreteGroup-path : {G H : ConcreteGroup ℓ} → B G ≡ B H → G ≡ H
ConcreteGroup-path {G = G} {H} p = go prop! prop! where
  go : PathP (λ i → is-connected∙ (p i)) (G .has-is-connected) (H .has-is-connected)
     → PathP (λ i → is-groupoid ⌞ p i ⌟) (G .has-is-groupoid) (H .has-is-groupoid)
     → G ≡ H
  go c g i .B = p i
  go c g i .has-is-connected = c i
  go c g i .has-is-groupoid = g i
```
-->

The [[delooping]] of a group is a concrete group. In fact, we will prove later that
*all* concrete groups arise as deloopings.

```agda
Concrete : ∀ {ℓ} → Group ℓ → ConcreteGroup ℓ
Concrete G .B = Deloop∙ G
Concrete G .has-is-connected = Deloop-is-connected
Concrete G .has-is-groupoid = squash
```

Another important example of a concrete group is the [[circle]]: the delooping of
the [[integers]].

```agda
opaque
  S¹-is-connected : is-connected∙ S¹∙
  S¹-is-connected = S¹-elim (inc refl) prop!

S¹-concrete : ConcreteGroup lzero
S¹-concrete .B = S¹∙
S¹-concrete .has-is-connected = S¹-is-connected
S¹-concrete .has-is-groupoid = hlevel 3
```

## The category of concrete groups

The notion of group *homomorphism* between two groups $G$ and $H$ gets translated
to, on the "concrete" side, [[*pointed* maps]] $\B{G} \to^\bullet \B{H}$.

The pointedness condition ensures that these maps behave like abstract group
homomorphisms; in particular, that they form a *set*.

```agda
ConcreteGroups-Hom-set
  : (G : ConcreteGroup ℓ) (H : ConcreteGroup ℓ')
  → is-set (B G →∙ B H)
ConcreteGroups-Hom-set G H (f , ptf) (g , ptg) p q =
  Σ-set-square hlevel! (funext-square (B-elim-contr G square))
  where
    open ConcreteGroup H using (H-Level-B)
    square : is-contr ((λ j → p j .fst (pt G)) ≡ (λ j → q j .fst (pt G)))
    square .centre i j = hcomp (∂ i ∨ ∂ j) λ where
      k (k = i0) → pt H
      k (i = i0) → p j .snd (~ k)
      k (i = i1) → q j .snd (~ k)
      k (j = i0) → ptf (~ k)
      k (j = i1) → ptg (~ k)
    square .paths _ = H .has-is-groupoid _ _ _ _ _ _
```

These naturally assemble into a [[category]].

```agda
ConcreteGroups : ∀ ℓ → Precategory (lsuc ℓ) ℓ
ConcreteGroups ℓ .Ob = ConcreteGroup ℓ
ConcreteGroups _ .Hom G H = B G →∙ B H
ConcreteGroups _ .Hom-set = ConcreteGroups-Hom-set
```

<details>
<summary>
The rest of the categorical structure is inherited from pointed functions, and
univalence follows from the [[univalence]] of the universe of groupoids.
</summary>

```agda
ConcreteGroups _ .id = id∙
ConcreteGroups _ ._∘_ = _∘∙_
ConcreteGroups _ .idr f = Σ-pathp refl (∙-idl _)
ConcreteGroups _ .idl f = Σ-pathp refl (∙-idr _)
ConcreteGroups _ .assoc (f , ptf) (g , ptg) (h , pth) = Σ-pathp refl $
  ⌜ ap f (ap g pth ∙ ptg) ⌝ ∙ ptf   ≡⟨ ap! (ap-∙ f _ _) ⟩
  (ap (f ⊙ g) pth ∙ ap f ptg) ∙ ptf ≡⟨ sym (∙-assoc _ _ _) ⟩
  ap (f ⊙ g) pth ∙ ap f ptg ∙ ptf   ∎

private
  iso→equiv : ∀ {a b} → Isomorphism (ConcreteGroups ℓ) a b → ⌞ a ⌟ ≃ ⌞ b ⌟
  iso→equiv im = Iso→Equiv (im .to .fst ,
    iso (im .from .fst) (happly (ap fst (im .invl))) (happly (ap fst (im .invr))))

ConcreteGroups-is-category : is-category (ConcreteGroups ℓ)
ConcreteGroups-is-category .to-path im = ConcreteGroup-path $
  Σ-pathp (ua (iso→equiv im)) (path→ua-pathp _ (im .to .snd))
ConcreteGroups-is-category {ℓ} .to-path-over im = ≅-pathp (ConcreteGroups ℓ) _ _ $
  Σ-pathp (funextP λ _ → path→ua-pathp _ refl)
    (λ i j → path→ua-pathp (iso→equiv im) (λ i → im .to .snd (i ∧ j)) i)
```
</details>

## Concrete vs. abstract

Our goal is now to prove that concrete groups and abstract groups are equivalent,
in the sense that there is an [[equivalence of categories]] between `ConcreteGroups`{.Agda}
and `Groups`{.Agda}.

Since we're dealing with groupoids, we can use the alternative definition of
the fundamental group that avoids set truncations.

```agda
module _ (G : ConcreteGroup ℓ) where
  open π₁Groupoid (B G) (G .has-is-groupoid)
    renaming (π₁ to π₁B; π₁≡π₀₊₁ to π₁B≡π₀₊₁)
    public
```

We define a [[functor]] from concrete groups to abstract groups.
The object mapping is given by taking the `fundamental group`{.Agda ident=π₁B}.
Given a pointed map $f : \B{G} \to^\bullet \B{H}$, we can `ap`{.Agda}ply it to a loop
on $\point{G}$ to get a loop on $f(\point{G})$; then, we use the fact that $f$
is pointed to get a loop on $\point{H}$ by [[conjugation]].

```agda
π₁F : Functor (ConcreteGroups ℓ) (Groups ℓ)
π₁F .F₀ = π₁B
π₁F .F₁ (f , ptf) .hom x = conj ptf (ap f x)
```

By some simple path yoga, this preserves multiplication, and the construction is
functorial:

```agda
π₁F .F₁ (f , ptf) .preserves .pres-⋆ x y =
  conj ptf ⌜ ap f (x ∙ y) ⌝             ≡⟨ ap! (ap-∙ f _ _) ⟩
  conj ptf (ap f x ∙ ap f y)            ≡⟨ conj-of-∙ _ _ _ ⟩
  conj ptf (ap f x) ∙ conj ptf (ap f y) ∎

π₁F .F-id = ext conj-refl
π₁F .F-∘ (f , ptf) (g , ptg) = ext λ x →
  conj (ap f ptg ∙ ptf) (ap (f ⊙ g) x)        ≡˘⟨ conj-∙ _ _ _ ⟩
  conj ptf ⌜ conj (ap f ptg) (ap (f ⊙ g) x) ⌝ ≡˘⟨ ap¡ (ap-conj f _ _) ⟩
  conj ptf (ap f (conj ptg (ap g x)))         ∎
```

We start by showing that `π₁F`{.Agda} is [[split essentially surjective]]. This is the
easy part: to build a concrete group out of an abstract group, we simply take its
`Deloop`{.Agda}ing, and use the fact that the fundamental group of the delooping
recovers the original group.

<!--
```agda
_ = Deloop
```
-->

```agda
π₁F-is-split-eso : is-split-eso (π₁F {ℓ})
π₁F-is-split-eso G .fst = Concrete G
π₁F-is-split-eso G .snd = path→iso (π₁B≡π₀₊₁ (Concrete G) ∙ sym (G≡π₁B G))
```

We now tackle the hard part: to prove that `π₁F`{.Agda} is [[fully faithful]].
In order to show that the action on morphisms is an equivalence, we need a way
of "delooping" a group homomorphism $f : \pi_1(\B{G}) \to \pi_1(\B{H})$ into a
pointed map $\B{G} \to^\bullet \B{H}$.

```agda
module Deloop-Hom {G H : ConcreteGroup ℓ} (f : Groups ℓ .Hom (π₁B G) (π₁B H)) where
  open ConcreteGroup H using (H-Level-B)
```

How can we build such a map? All we know about $\B{G}$ is that it is a pointed connected
groupoid, and thus that it comes with the elimination principle `B-elim-contr`{.Agda}.
This suggests that we need to define a type family $C : \B{G} \to \ty$ such that
$C(\point{G})$ is contractible, conclude that $\forall x. C(x)$ holds
and extract a map $\B{G} \to^\bullet \B{H}$ from that.
The following construction is adapted from [@Symmetry, §4.10]:

```agda
  record C (x : ⌞ G ⌟) : Type ℓ where
    constructor mk
    field
      y : ⌞ H ⌟
      p : pt G ≡ x → pt H ≡ y
      f-p : (ω : pt G ≡ pt G) (α : pt G ≡ x) → p (ω ∙ α) ≡ f # ω ∙ p α
```

Our family sends a point $x : \B{G}$ to a point $y : \B{H}$ with a function $p$ that
sends based paths ending at $x$ to based paths ending at $y$, with the additional
constraint that $p$ must "extend" $f$, in the sense that a loop on the left can be
factored out using $f$.

For the centre of contraction, we simply pick $p$ to be $f$, sending loops on
$\point{G}$ to loops on $\point{H}$.

```agda
  C-contr : is-contr (C (pt G))
  C-contr .centre .C.y = pt H
  C-contr .centre .C.p = f .hom
  C-contr .centre .C.f-p = f .preserves .pres-⋆
```

As it turns out, such a structure is entirely determined by the pair
$(y, p(\refl) : \point{H} \equiv y)$, which means it is contractible.

```agda
  C-contr .paths (mk y p f-p) i = mk (pt≡y i) (funextP f≡p i) (□≡□ i) where
    pt≡y : pt H ≡ y
    pt≡y = p refl

    f≡p : ∀ ω → Square refl (f # ω) (p ω) (p refl)
    f≡p ω = ∙-filler (f # ω) (p refl) ▷ (sym (f-p ω refl) ∙ ap p (∙-idr ω))

    □≡□ : PathP (λ i → ∀ ω α → f≡p (ω ∙ α) i ≡ f # ω ∙ f≡p α i) (f .preserves .pres-⋆) f-p
    □≡□ = is-prop→pathp (λ i → hlevel 1) _ _
```

We can now apply the elimination principle and unpack our data:

```agda
  c : ∀ x → C x
  c = B-elim-contr G C-contr

  g : B G →∙ B H
  p : {x : ⌞ G ⌟} → pt G ≡ x → pt H ≡ g .fst x

  g .fst x = c x .C.y
  g .snd = sym (p refl)

  p {x} = c x .C.p

  f-p : (ω : pt G ≡ pt G) (α : pt G ≡ pt G) → p (ω ∙ α) ≡ f # ω ∙ p α
  f-p = c (pt G) .C.f-p
```

In order to show that this is a delooping of $f$ (i.e. that $\Pi_1(g) \equiv f$),
we need one more thing: that $p$ extends $g$ on the *right*. We get this essentially
for free, by path induction, because $p(α)$ ends at $g(x)$ by definition.

```agda
  p-g : (α : pt G ≡ pt G) {x' : ⌞ G ⌟} (l : pt G ≡ x')
      → p (α ∙ l) ≡ p α ∙ ap (g .fst) l
  p-g α = J (λ _ l → p (α ∙ l) ≡ p α ∙ ap (g .fst) l)
    (ap p (∙-idr _) ∙ sym (∙-idr _))
```

Since $g$ is pointed by $p(\refl)$, this lets us conclude that we have found a
right inverse to $\Pi_1$:

```agda
  f≡apg : (ω : pt G ≡ pt G) → Square (p refl) (f # ω) (ap (g .fst) ω) (p refl)
  f≡apg ω = commutes→square $
    p refl ∙ ap (g .fst) ω ≡˘⟨ p-g refl ω ⟩
    p (refl ∙ ω)           ≡˘⟨ ap p ∙-id-comm ⟩
    p (ω ∙ refl)           ≡⟨ f-p ω refl ⟩
    f # ω ∙ p refl         ∎

  rinv : π₁F .F₁ {G} {H} g ≡ f
  rinv = ext λ ω → pathp→conj (symP (f≡apg ω))
```

We are most of the way there. In order to get a proper equivalence, we must check that
delooping $\Pi_1(f)$ gives us back the same pointed map $f$.

We use the same trick, building upon what we've done before: start by defining
a family that asserts that $p_x$ agrees with $f$ *all the way*, not just on loops:

```agda
module Deloop-Hom-π₁F {G H : ConcreteGroup ℓ} (f : B G →∙ B H) where
  open Deloop-Hom {G = G} {H} (π₁F .F₁ {G} {H} f) public
  open ConcreteGroup H using (H-Level-B)

  C' : ∀ x → Type _
  C' x = Σ (f .fst x ≡ g .fst x) λ eq
       → (α : pt G ≡ x) → Square (f .snd) (ap (f .fst) α) (p α) eq
```

This is a [[property]], and $\point{G}$ has it:

```agda
  C'-contr : is-contr (C' (pt G))
  C'-contr .centre .fst = f .snd ∙ sym (g .snd)
  C'-contr .centre .snd α = commutes→square $
    f .snd ∙ p ⌜ α ⌝                                ≡˘⟨ ap¡ (∙-idr _) ⟩
    f .snd ∙ ⌜ p (α ∙ refl) ⌝                       ≡⟨ ap! (f-p α refl) ⟩
    f .snd ∙ conj (f .snd) (ap (f .fst) α) ∙ p refl ≡˘⟨ ∙-extendl (∙-swapl (sym (conj-defn _ _))) ⟩
    ap (f .fst) α ∙ f .snd ∙ p refl                 ∎
  C'-contr .paths (eq , eq-paths) = Σ-prop-path! $
    sym (∙-unique _ (transpose (eq-paths refl)))
```

Using the elimination principle again, we get enough information about `g` to conclude
that it is equal to `f`, so that we have a left inverse.

```agda
  c' : ∀ x → C' x
  c' = B-elim-contr G C'-contr

  g≡f : ∀ x → g .fst x ≡ f .fst x
  g≡f x = sym (c' x .fst)
```

The homotopy `g≡f` is [[pointed]] by `definition`{.Agda ident=C'-contr}, but we
need to bend the path into a `Square`{.Agda}:

```agda
  β : g≡f (pt G) ≡ sym (f .snd ∙ sym (g .snd))
  β = ap (sym ⊙ fst) (sym (C'-contr .paths (c' (pt G))))

  ptg≡ptf : Square (g≡f (pt G)) (g .snd) (f .snd) refl
  ptg≡ptf i j = hcomp (∂ i ∨ ∂ j) λ where
    k (k = i0) → ∙-filler (f .snd) (sym (g .snd)) (~ j) (~ i)
    k (i = i0) → g .snd j
    k (i = i1) → f .snd (j ∧ k)
    k (j = i0) → β (~ k) i
    k (j = i1) → f .snd (~ i ∨ k)

  linv : g ≡ f
  linv = funext∙ g≡f ptg≡ptf
```

*Phew*. At last, `π₁F`{.Agda} is fully faithful.

```agda
π₁F-is-ff : is-fully-faithful (π₁F {ℓ})
π₁F-is-ff {ℓ} {G} {H} = is-iso→is-equiv $ iso
  (Deloop-Hom.g {G = G} {H})
  (Deloop-Hom.rinv {G = G} {H})
  (Deloop-Hom-π₁F.linv {G = G} {H})
```

We've shown that `π₁F`{.Agda} is fully faithful and essentially surjective;
this lets us conclude with the desired equivalence.

```agda
π₁F-is-equivalence : is-equivalence (π₁F {ℓ})
π₁F-is-equivalence = ff+split-eso→is-equivalence
  (λ {G} {H} → π₁F-is-ff {_} {G} {H})
  π₁F-is-split-eso

π₁B-is-equiv : is-equiv (π₁B {ℓ})
π₁B-is-equiv = is-cat-equivalence→equiv-on-objects
  ConcreteGroups-is-category
  Groups-is-category
  π₁F-is-equivalence

module Concrete≃Abstract {ℓ} = Equiv (_ , π₁B-is-equiv {ℓ})
```

## Concrete abelian groups

A concrete [[abelian group]] is, unsurprisingly, a concrete group in which
concatenation of loops at the base point is commutative.

```agda
module _ {ℓ} (G : ConcreteGroup ℓ) where
  is-concrete-abelian : Type ℓ
  is-concrete-abelian = ∀ (p q : pt G ≡ pt G) → p ∙ q ≡ q ∙ p
```

This is a property:

```agda
  open ConcreteGroup G using (H-Level-B)

  is-concrete-abelian-is-prop : is-prop is-concrete-abelian
  is-concrete-abelian-is-prop = hlevel 1
```

As an easy consequence, in an abelian group $\B{G}$, we can fill any square
that has equal opposite sides.

```agda
  concrete-abelian→square
    : is-concrete-abelian
    → {x : ⌞ B G ⌟} → (p q : x ≡ x) → Square p q q p
  concrete-abelian→square ab {x} = connected∙-elim-prop
    {P = λ x → (p q : x ≡ x) → Square p q q p}
    (G .has-is-connected)
    (hlevel 1)
    (λ p q → commutes→square (ab p q))
    x
```

Still unsurprisingly, the delooping of an abelian group is abelian.

```agda
Deloop-abelian
  : ∀ {ℓ} {G : Group ℓ}
  → is-commutative-group G → is-concrete-abelian (Concrete G)
Deloop-abelian G-ab = ∙-comm _ G-ab
```

The circle is another example, being the delooping of $\mathbb{Z}$.

```agda
π₁-abelian→abelian
  : ∀ {ℓ} {G : ConcreteGroup ℓ}
  → is-commutative-group (π₁B G) → is-concrete-abelian G
π₁-abelian→abelian {G = G} π₁G-ab = subst is-concrete-abelian
  (Concrete≃Abstract.η G)
  (Deloop-abelian π₁G-ab)

S¹-concrete-abelian : is-concrete-abelian S¹-concrete
S¹-concrete-abelian = π₁-abelian→abelian {G = S¹-concrete}
  (subst is-commutative-group
    (sym π₁S¹≡ℤ)
    (Abelian→Group-on-abelian (ℤ-ab .snd)))
```

## First abelian group cohomology

When $H$ is a concrete abelian group, something interesting happens: for any
other concrete group $G$, the set of pointed maps $\B{G} \to^\bullet \B{H}$ (i.e.
group homomorphisms from $G$ to $H$) turns out to be equivalent to the
[[set truncation]] of the type of *un*pointed maps, $\|\B{G} \to \B{H}\|_0$.

This is a special case of a theorem that relates this set truncation with the set
of orbits of the action of the *inner automorphism group* of $H$ on the set of group
homomorphisms $\B{G} \to^\bullet \B{H}$. We do not prove this here, but see
[@Symmetry, theorem 5.12.2]. In the special case that $H$ is abelian, its inner
automorphism group is trivial, and we can avoid quotienting.

In even fancier language, it is also a computation of the first *cohomology group*
of $G$ with coefficients in $H$, hence we adopt the notation
$H^1(G, H) = \|\B{G} \to \B{H}\|_0$.

```agda
H¹[_,_] : ∀ {ℓ ℓ'} → ConcreteGroup ℓ → ConcreteGroup ℓ' → Type (ℓ ⊔ ℓ')
H¹[ G , H ] = ∥ (⌞ B G ⌟ → ⌞ B H ⌟) ∥₀
```

First, note that there is always a natural map $(\B{G} \to^\bullet \B{H}) \to
H^1(G, H)$ that just forgets the pointing path.

```agda
class
  : ∀ {ℓ ℓ'} (G : ConcreteGroup ℓ) (H : ConcreteGroup ℓ')
  → (B G →∙ B H) → H¹[ G , H ]
class G H (f , _) = inc f
```

Now assume $H$ is abelian; we will show that this map is injective and surjective,
so that it is an equivalence of sets.

<!--
```agda
module _ {ℓ ℓ'}
  (G : ConcreteGroup ℓ)
  (H : ConcreteGroup ℓ') (H-ab : is-concrete-abelian H)
  where
  open ConcreteGroup H using (H-Level-B)
```
-->

Surjectivity is the easy part: since $H$ is connected, every map is merely
homotopic to a pointed map.

```agda
  class-surjective : is-surjective (class G H)
  class-surjective = ∥-∥₀-elim (λ _ → hlevel 2) λ f → do
    ptf ← H .has-is-connected (f (pt G))
    inc ((f , ptf) , refl)
```

For injectivity, we restrict our attention to the case of two pointed maps whose
underlying maps are *definitionally* equal. In other words, we prove that any
two pointings of $f$ (say $p, q : f(\point{G}) \equiv \point{H}$) yield
equal *pointed* maps.

In order to define our underlying homotopy, we proceed by induction: since
$G$ is a pointed connected type, it suffices to give a path $\alpha :
f(\point{G}) \equiv f(\point{G})$ and to show that every loop $l : \point{G}
\equiv \point{G}$ respects this identification, in the sense of the
following square:

~~~{.quiver}
\[\begin{tikzcd}
  {f(\point{G})} & {f(\point{G})} \\
  {f(\point{G})} & {f(\point{G})}
  \arrow["{\alpha}", from=1-1, to=1-2]
  \arrow["{\alpha}"', from=2-1, to=2-2]
  \arrow["{f(l)}"', from=1-1, to=2-1]
  \arrow["{f(l)}", from=1-2, to=2-2]
\end{tikzcd}\]
~~~

Since our homotopy additionally has to be *pointed*, we know that we must have
$\alpha = p \bullet q^{-1}$. This is where the fact that $H$ is abelian
comes in: the above square has equal opposite sides, so it automatically commutes.

```agda
  class-injective
    : ∀ f → (p q : f (pt G) ≡ pt H)
    → Path (B G →∙ B H) (f , p) (f , q)
  class-injective f p q = Σ-pathp
    (funext E.elim)
    (transpose (symP (∙→square'' E.elim-β-point)))
    where
      α : f (pt G) ≡ f (pt G)
      α = p ∙ sym q

      coh : ∀ (l : pt G ≡ pt G) → Square (ap f l) α α (ap f l)
      coh l = concrete-abelian→square H H-ab (ap f l) α

      module E = connected∙-elim-set {P = λ g → f g ≡ f g}
        (G .has-is-connected) (hlevel 2) α coh
```

By a quick path induction, we can conclude that `class`{.Agda} is an equivalence
between sets.

```agda
  class-is-equiv : is-equiv (class G H)
  class-is-equiv = injective-surjective→is-equiv! (inj _ _) class-surjective
    where
      inj : ∀ f g → class G H f ≡ class G H g → f ≡ g
      inj (f , ptf) (g , ptg) f≡g = ∥-∥-rec
        (ConcreteGroups-Hom-set G H _ _)
        (λ f≡g → J (λ g _ → ∀ ptg → (f , ptf) ≡ (g , ptg))
                   (class-injective f ptf)
                   f≡g ptg)
        (∥-∥₀-path.to f≡g)

  first-concrete-abelian-group-cohomology
    : (B G →∙ B H) ≃ H¹[ G , H ]
  first-concrete-abelian-group-cohomology
    = class G H , class-is-equiv
```

Translating this across our equivalence of categories gives a similar statement
for abstract groups.

<!--
```agda
module _ {ℓ}
  (G : Group ℓ)
  (H : Group ℓ) (H-ab : is-commutative-group H)
  where
```
-->

```agda
  Deloop-hom-equiv : (Deloop∙ G →∙ Deloop∙ H) ≃ Hom (Groups ℓ) G H
  Deloop-hom-equiv = ff+split-eso→hom-equiv π₁F
    (λ {G} {H} → π₁F-is-ff {_} {G} {H})
    π₁F-is-split-eso
    G H .snd .snd

  first-abelian-group-cohomology
    : H¹[ Concrete G , Concrete H ] ≃ Hom (Groups ℓ) G H
  first-abelian-group-cohomology =
    first-concrete-abelian-group-cohomology
      (Concrete G) (Concrete H) (Deloop-abelian H-ab) e⁻¹
    ∙e Deloop-hom-equiv
```
