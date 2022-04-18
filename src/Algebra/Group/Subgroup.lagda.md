```agda
open import Algebra.Group.Cat.FinitelyComplete
open import Algebra.Group.Cat.Base
open import Algebra.Prelude
open import Algebra.Group

open import Cat.Diagram.Equaliser.Kernel

open import Data.Power

module Algebra.Group.Subgroup where
```

<!--
```agda
private variable
  ℓ ℓ' : Level
  G : Group ℓ
```
-->

# Subgroups

A **subgroup** $m$ of a group $G$ is a [monomorphism] $H \xto{m} G$,
that is, an object of the [poset of subobjects] $\Sub(G)$. Since group
homomorphisms are injective exactly when their underlying function is an
[embedding], we can alternatively describe this as a condition on a
predicate $G \to \prop$.

[monomorphism]: Cat.Morphism.html#monos
[poset of subobjects]: Cat.Thin.Instances.Sub.html
[embedding]: 1Lab.Equiv.Embedding.html

```agda
Subgroup : Group ℓ → Type (lsuc ℓ)
Subgroup {ℓ = ℓ} G = Precategory.Ob (Subobj (Groups ℓ) G)
```

A proposition $H : G \to \prop$ of a group $(G, \star)$ **represents a
subgroup** if it contains the group `unit`{.Agda}, is closed under
multiplication, and is closed under inverses.

```agda
record represents-subgroup (G : Group ℓ) (H : ℙ (G .fst)) : Type ℓ where
  open Group-on (G .snd)

  field
    has-unit : unit ∈ H
    has-⋆    : ∀ {x y} → x ∈ H → y ∈ H → (x ⋆ y) ∈ H
    has-inv  : ∀ {x} → x ∈ H → x ⁻¹ ∈ H
```

If $H$ represents a subgroup, then its total space $\Sigma H$ inherits a
group structure from $G$, and the first projection $\Sigma H \to G$ is a
group homormophism.

```agda
rep-subgroup→group-on
  : (H : ℙ (G .fst)) → represents-subgroup G H → Group-on (Σ[ x ∈ G .fst ] x ∈ H)
rep-subgroup→group-on {G = G} H sg =
  make-group
    (Σ-is-hlevel 2 has-is-set λ x → is-prop→is-set (H x .is-tr))
    (unit , has-unit)
    (λ { (x , xin) (y , yin) → x ⋆ y , has-⋆ xin yin} )
    (λ { (x , xin) → (x ⁻¹ , has-inv xin) })
    (λ x y z → Σ-prop-path (λ x → H x .is-tr) (sym associative))
    (λ x → Σ-prop-path (λ x → H x .is-tr) inversel)
    (λ x → Σ-prop-path (λ x → H x .is-tr) inverser)
    (λ x → Σ-prop-path (λ x → H x .is-tr) idl)
  where open Group-on (G .snd)
        open represents-subgroup sg

predicate→subgroup : (H : ℙ (G .fst)) → represents-subgroup G H → Subgroup G
predicate→subgroup {G = G} H p = cut map , ism where
  map : Groups.Hom (Σ (∣_∣ ⊙ H) , rep-subgroup→group-on H p) G
  map .fst = fst
  map .snd .Group-hom.pres-⋆ x y = refl

  ism : Groups.is-monic map
  ism g h p = Forget-is-faithful
    (embedding→monic (Subset-proj-embedding (is-tr ⊙ H)) (fst g) (fst h) (ap fst p))
```

# Kernels and Images

To a group homomorphism $f : A \to B$ we can associate two canonical
subgroups, one of $A$ and one of $B$: $f$'s [**image**], written $\im
f$, is the subgroup of $B$ "reachable by mapping through $f$", and $f$'s
[**kernel**], written $\ker f$, is the subgroup of $A$ which $f$ sends
to the unit.

[**image**]: Cat.Diagram.Image.html
[**kernel**]: Cat.Diagram.Equaliser.Kernel.html

The kernel can be cheapily described as a [limit]: It is the [equaliser]
of $f$ and the [zero morphism] --- which, recall, is the unique map $A
\to B$ which breaks down as $A \to 0 \to B$.

```agda
module _ {ℓ} where
  open Canonical-kernels (Groups ℓ) ∅ᴳ Groups-equalisers public

  Ker-subgroup : ∀ {A B : Group ℓ} → Groups.Hom A B → Subgroup A
  Ker-subgroup f = cut kernel , Groups.is-equaliser→is-monic _ has-is-kernel where
    open Kernel (Ker f)
```

[limit]: Cat.Diagram.Limit.Base.html
[zero morphism]: Cat.Diagram.Zero.html
[equaliser]: Cat.Diagram.Equaliser.html

Every group homomorphism $f : A \to B$ has an _image_ $\im f$, defined
by equipping its set-theoretic `image`{.Agda} with a group structure
inherited from $B$. More concretely, we can describe the elements of
$\im f$ as the "mere fibres" of $f$: They consist of a point $y : B$,
together with (the truncation of) a fibre of $f$ over $y$. We multiply
$x$ (in the fibre over $a$) with $y$ (in the fibre over $b$), giving the
element $xy$ in the fibre over $ab$.

[image]: Cat.Diagram.Image.html

<!--
```agda
module _ {ℓ} {A B : Group ℓ} (f : Groups.Hom A B) where
  private
    module A = Group-on (A .snd)
    module B = Group-on (B .snd)
    module f = Group-hom (f .snd)

    Tpath : {x y : image (f .fst)} → x .fst ≡ y .fst → x ≡ y
    Tpath {x} {y} p = Σ-prop-path (λ _ → squash) p

    abstract
      Tset : is-set (image (f .fst))
      Tset = hlevel 2

    module Kerf = Kernel (Ker f)
```
-->

For reasons that will become clear later, we denote the image of $f$,
when regarded as its own group, by $A/\ker(f)$, and reserve the notation
$\im f$ for that group regarded _as a subgroup of $B$_.

<details>
<summary>The construction of a group structure on $A/\ker(f)$ is
unsurprising, so we leave it in this `<details>` tag for the curious
reader.</summary>

```agda
    T : Type ℓ
    T = image (f .fst)

  A/ker[_] : Group ℓ
  A/ker[_] = T , grp where
    unit : T
    unit = B.unit , inc (A.unit , f.pres-id)

    inv : T → T
    inv (x , p) = x B.⁻¹ ,
      ∥-∥-map (λ { (y , p) → y A.⁻¹ , f.pres-inv ∙ ap B._⁻¹ p }) p

    mul : T → T → T
    mul (x , xp) (y , yp) = x B.⋆ y ,
      ∥-∥-elim₂ (λ _ _ → squash)
        (λ { (x* , xp) (y* , yp)
           → inc (x* A.⋆ y* , f.pres-⋆ _ _ ∙ ap₂ B._⋆_ xp yp) })
        xp yp

    grp : Group-on T
    grp = make-group Tset unit mul inv
      (λ x y z → Tpath (sym B.associative))
      (λ x → Tpath B.inversel) (λ x → Tpath B.inverser) λ x → Tpath B.idl
```

</details>

That the canonical inclusion map $A/\ker(f) \mono B$ deserves the name
"image" comes from $f$ breaking down as a (regular) epimorphism into
$\im f$ (written `A→im`{.Agda}), followed by that map:

$$
(A \xto{f} B) = (A \xepi{f} A/\ker(f) \mono B)
$$

```agda
  A→im : Groups.Hom A A/ker[_]
  A→im .fst x = f .fst x , inc (x , refl)
  A→im .snd .Group-hom.pres-⋆ x y = Tpath (f.pres-⋆ _ _)

  im→B : Groups.Hom A/ker[_] B
  im→B .fst (b , _) = b
  im→B .snd .Group-hom.pres-⋆ x y = refl
```

When this monomorphism is taken as primary, we refer to $A/\ker(f)$ as
$\im f$.

```agda
  Im[_] : Subgroup B
  Im[_] = cut im→B , im↪B where
    im↪B : Groups.is-monic im→B
    im↪B = injective-group-hom im→B Tpath
```

The reason for denoting the set-theoretic image of $f : A \to B$ (which
is a subobject **of $B$**, equipped with $B$'s group operation) by
$A/\ker(f)$ is the **first isomorphism theorem** (though we phrase it
more categorically): The image of $f$ serves as a [quotient] for (the
[congruence] generated by) $\ker f$.

[quotient]: Cat.Diagram.Coequaliser.html
[congruence]: Cat.Diagram.Congruence.html

**Note**: In more classical texts, the first isomorphism theorem is
phrased in terms of two _pre-existing_ objects $A/\ker(f)$ (defined as
the set of _cosets_ of $\ker(f)$ regarded as a subgroup) and $\im f$
(defined as above).  Here we have opted for a more categorical phrasing
of that theorem: We know what the universal property of $A/\ker(f)$ is
--- namely that it is a specific colimit --- so the specific
construction used to implement it does not matter.

```agda
  1st-iso-theorem : Groups.is-coequaliser (Groups.Zero.zero→ ∅ᴳ) Kerf.kernel A→im
  1st-iso-theorem = coeq where
    open Groups
    open is-coequaliser
    module Ak = Group-on (A/ker[_] .snd)
```

More specifically, in a diagram like the one below, the indicated dotted
arrow _always_ exists and is unique, witnessing that the map $A \epi
A/\ker(f)$ is a coequaliser (hence that it is a regular epi, as we
mentioned above).

~~~{.quiver}
\[\begin{tikzcd}
  {\ker f} & A & {A/\ker(f)} \\
  && F
  \arrow["0", shift left=2, from=1-1, to=1-2]
  \arrow[shift right=2, hook, from=1-1, to=1-2]
  \arrow[two heads, from=1-2, to=1-3]
  \arrow[dashed, from=1-3, to=2-3]
  \arrow["{e'}"', from=1-2, to=2-3]
\end{tikzcd}\]
~~~

The condition placed on $e'$ is that $0 = e' \circ \ker f$; This means
that it, like $f$, sends everything in $\ker f$ to zero (this is the
defining property of $\ker f$). Note that in the code below we do not
elide the zero composite $e' \circ 0$.

```agda
    elim
      : ∀ {F} {e' : Groups.Hom A F}
          (p : e' Groups.∘ Zero.zero→ ∅ᴳ ≡ e' Groups.∘ Kerf.kernel)
      → ∀ {x} → ∥ fibre (f .fst) x ∥ → _
    elim {F = F} {e' = e' , gh} p {x} =
      ∥-∥-rec-set (e' ⊙ fst) const (F .snd .Group-on.has-is-set) where abstract
      module e' = Group-hom gh
      module F = Group-on (F .snd)
```

To eliminate from under a [propositional truncation], we must prove that
the map $e'$ is constant when thought of as a map $f^*(x) \to F$; In
other words, it means that $e'$ is "independent of the choice of
representative". This follows from algebraic manipulation of group
homomorphisms + the assumed identity $0 = e' \circ \ker f$;

```agda
      const′ : ∀ (x y : fibre (f .fst) x)
             → e' (x .fst) F.— e' (y .fst) ≡ F.unit
      const′ (y , q) (z , r) =
        e' y F.— e' z  ≡˘⟨ e'.pres-diff ⟩
        e' (y A.— z)   ≡⟨ happly (sym (ap fst p)) (y A.— z , aux) ⟩
        e' A.unit      ≡⟨ e'.pres-id ⟩
        F.unit         ∎
        where
```

This assumption allows us to reduce "show that $e'$ is constant on a
specific subset" to "show that $f(y - z) = 0$ when $f(y) = f(z) = x$";
But that's just algebra, hence uninteresting:

```agda
          aux : f .fst (y A.— z) ≡ B.unit
          aux =
            f .fst (y A.— z)        ≡⟨ f.pres-diff ⟩
            f .fst y B.— f .fst z   ≡⟨ ap₂ B._—_ q r ⟩
            x B.— x                 ≡⟨ B.inverser ⟩
            B.unit                  ∎

      const : ∀ (x y : fibre (f .fst) x) → (e' (x .fst)) ≡ (e' (y .fst))
      const a b = F.zero-diff (const′ a b)
```

The rest of the construction is almost tautological: By _definition_, if
$x : \ker f$, then $f(x) = 0$, so the quotient map $A \epi A/\ker(f)$
does indeed coequalise $\ker f \mono A$ and $0$. As a final word on the
rest of the construction, most of it is applying induction
(`∥-∥-elim`{.Agda} and friends) so that our colimiting map `elim`{.Agda}
will compute.

```agda
    coeq : is-coequaliser _ _ A→im
    coeq .coequal = Forget-is-faithful (funext path) where
      path : (x : Kerf.ker .fst) → A→im .fst A.unit ≡ A→im .fst (x .fst)
      path (x* , p) = Tpath (f.pres-id ∙ sym p)

    coeq .coequalise {F = F} {e′ = e'} p = gh where
      module F = Group-on (F .snd)
      module e' = Group-hom (e' .snd)

      gh : Groups.Hom _ _
      gh .fst (x , t) = elim {e' = e'} p t
      gh .snd .Group-hom.pres-⋆ (x , q) (y , r) =
        ∥-∥-elim₂
          {P = λ q r → elim p (((x , q) Ak.⋆ (y , r)) .snd) ≡ elim p q F.⋆ elim p r}
          (λ _ _ → F.has-is-set _ _) (λ x y → e'.pres-⋆ _ _) q r

    coeq .universal = Forget-is-faithful refl

    coeq .unique {F} {p = p} {colim = colim} prf = Forget-is-faithful (funext path)
      where abstract
        module F = Group-on (F .snd)
        path : ∀ x → colim .fst x ≡ elim p (x .snd)
        path (x , t) =
          ∥-∥-elim
            {P = λ q → colim .fst (x , q) ≡ elim p q}
            (λ _ → F.has-is-set _ _)
            (λ { (f , fp) → ap (colim .fst) (Σ-prop-path (λ _ → squash) (sym fp))
                          ∙ sym (happly (ap fst prf) f) })
            t
```

## Representing kernels

If an evil wizard kidnaps your significant others and demands that you
find out whether a predicate $P : G \to \prop$ is a kernel, how would
you go about doing it? Well, I should point out that no matter how evil
the wizard is, they are still human: The predicate $P$ definitely
represents a subgroup, in the sense introduced
[above](#represents-subgroup) --- so there's definitely a group
homomorphism $\Sigma G \mono G$. All we need to figure out is whether
there exists a group $H$ and a map $f : G \to H$, such that $\Sigma G
\cong \ker f$ as subgroups of $G$.

We begin by assuming that we have a kernel and investigating some
properties that the fibres of its inclusion have. Of course, the fibre
over $0$ is inhabited, and they are closed under multiplication and
inverses, though we shall not make note of that here).

```agda
module _ {ℓ} {A B : Group ℓ} (f : Groups.Hom A B) where private
  module Ker[f] = Kernel (Ker f)
  module f = Group-hom (f .snd)
  module A = Group-on (A .snd)
  module B = Group-on (B .snd)

  kerf : Ker[f].ker .fst → A .fst
  kerf = Ker[f].kernel .fst

  has-zero : fibre kerf A.unit
  has-zero = (A.unit , f.pres-id) , refl

  has-⋆ : ∀ {x y} → fibre kerf x → fibre kerf y → fibre kerf (x A.⋆ y)
  has-⋆ ((a , p) , q) ((b , r) , s) =
    (a A.⋆ b , f.pres-⋆ _ _ ·· ap₂ B._⋆_ p r ·· B.idl) ,
    ap₂ A._⋆_ q s
```

It turns out that $\ker f$ is also closed under _conjugation_ by
elements of the enveloping group, in that if $f(x) = 1$ (quickly
switching to "multiplicative" notation for the unit), then $f(yxy^{-1})$
must be $1$ as well: for we have $$f(y)f(x)f(y^{-1}) = f(y)1f(y^{-1}) =
f(yy^{-1}) = f(1) = 1$$.

```agda
  has-conjugate : ∀ {x y} → fibre kerf x → fibre kerf (y A.⋆ x A.⋆ y A.⁻¹)
  has-conjugate {x} {y} ((a , p) , q) = (_ , path) , refl where
    path =
      f .fst (y A.⋆ (x A.— y))             ≡⟨ ap (f .fst) A.associative ⟩
      f .fst ((y A.⋆ x) A.— y)             ≡⟨ f.pres-diff ⟩
      f .fst (y A.⋆ x) B.— f .fst y        ≡⟨ ap (B._⋆ _) (f.pres-⋆ y x) ⟩
      (f .fst y B.⋆ f .fst x) B.— f .fst y ≡⟨ ap (B._⋆ _) (ap (_ B.⋆_) (ap (f .fst) (sym q) ∙ p) ∙ B.idr) ⟩
      f .fst y B.— f .fst y                ≡˘⟨ f.pres-diff ⟩
      f .fst (y A.— y)                     ≡⟨ ap (f .fst) A.inverser ∙ f.pres-id ⟩
      B.unit                               ∎
```

It turns out that this last property is enough to pick out exactly the
kernels amongst the representations of subgroups: If $H$ is closed under
conjugation, then $H$ generates an equivalence relation on the set
underlying $G$ (namely, $(x - y) \in H$), and equip the [quotient] of
this equivalence relation with a group structure. The kernel of the
quotient map $G \to G/H$ is then $H$. We call a predicate representing a
kernel a **normal subgroup**, and we denote this in shorthand by $H
\unlhd G$.

[quotient]: Data.Set.Coequaliser.html

```agda
record normal-subgroup (G : Group ℓ) (H : ℙ (G .fst)) : Type ℓ where
  open Group-on (G .snd)
  field
    has-rep : represents-subgroup G H
    has-conjugate : ∀ {x y} → x ∈ H → (y ⋆ x ⋆ y ⁻¹) ∈ H

  has-conjugatel : ∀ {x y} → y ∈ H → ((x ⋆ y) ⋆ x ⁻¹) ∈ H
  has-conjugatel yin = subst (_∈ H) associative (has-conjugate yin)

  has-comm : ∀ {x y} → (x ⋆ y) ∈ H → (y ⋆ x) ∈ H
  has-comm {x = x} {y} ∈ = subst (_∈ H) p (has-conjugate ∈) where
    p = x ⁻¹ ⋆ (x ⋆ y) ⋆ x ⁻¹ ⁻¹ ≡⟨ ap₂ _⋆_ refl (sym associative) ∙ (λ i → x ⁻¹ ⋆ x ⋆ y ⋆ inv-inv {x = x} i) ⟩
        x ⁻¹ ⋆ x ⋆ y ⋆ x         ≡⟨ associative ⟩
        (x ⁻¹ ⋆ x) ⋆ y ⋆ x       ≡⟨ ap₂ _⋆_ inversel refl ∙ idl ⟩
        y ⋆ x                    ∎

  open represents-subgroup has-rep public
```

So, suppose we have a normal subgroup $H \unlhd G$. We define the
underlying type of the quotient $G/H$ to be the quotient of the relation
$R(x, y) = (x - y) \in H$; It can be equipped with a group operation
inherited from $G$, but this is _incredibly_ tedious to do.

<!--
```agda
module _ (Grp : Group ℓ) {H : ℙ (Grp .fst)} (N : normal-subgroup Grp H) where
  open normal-subgroup N
  open Group-on (Grp .snd) renaming (inverse to inv)
  private
    G0 = Grp .fst
    rel : G0 → G0 → Type _
    rel x y = (x ⋆ y ⁻¹) ∈ H

    rel-refl : ∀ x → rel x x
    rel-refl _ = subst (_∈ H) (sym inverser) has-unit
```
-->

```agda
    G/H : Type _
    G/H = G0 / rel

    op : G/H → G/H → G/H
    op = Quot-op₂ rel-refl rel-refl _⋆_ (λ w x y z a b → rem₃ y z w x b a) where
```

To prove that the group operation `_⋆_`{.Agda} descends to the quotient,
we prove that it takes related inputs to related outputs — a
characterisation of binary operations on quotients we can invoke since
the relation we’re quotienting by is reflexive. It suffices to show that
$(yw - zx) \in H$ whenever $w - x$ and $y - z$ are both in $H$, which is
a tedious but straightforward calculation:

```agda
      module
        _ (w x y z : G0)
          (w-x∈ : (w ⋆ inv x) ∈ H)
          (y-z∈ : (y ⋆ inv z) ∈ H) where abstract
        rem₁ : ((w — x) ⋆ (inv z ⋆ y)) ∈ H
        rem₁ = has-⋆ w-x∈ (has-comm y-z∈)

        rem₂ : ((w ⋆ (inv x — z)) ⋆ y) ∈ H
        rem₂ = subst (_∈ H) (associative ∙ ap (_⋆ y) (sym associative)) rem₁

        rem₃ : ((y ⋆ w) — (z ⋆ x)) ∈ H
        rem₃ = subst (_∈ H) (associative ∙ ap₂ _⋆_ refl (sym inv-comm))
          (has-comm rem₂)
```

To define inverses on the quotient, it suffices to show that whenever
$(x - y) \in H$, we also have $(x^{-1} - y) \in H$.

```agda
    inverse : G/H → G/H
    inverse =
      Coeq-rec squash (λ x → inc (inv x)) λ { (x , y , r) → quot (p x y r) }
      where abstract
        p : ∀ x y → (x — y) ∈ H → (inv x — inv y) ∈ H
        p x y r = has-comm (subst (_∈ H) inv-comm (has-inv r))
```

Even after this tedious algebra, it still remains to show that the
operation is associative and has inverses. Fortunately, since equality
in a group is a proposition, these follow from the group axioms on $G$
rather directly:

```agda
    Group-on-G/H : Group-on G/H
    Group-on-G/H = make-group squash (inc unit) op inverse
      (Coeq-elim-prop₃ (λ _ _ _ → squash _ _)
        λ x y z i → inc (associative {x = x} {y} {z} (~ i)))
      (Coeq-elim-prop (λ _ → squash _ _) λ x i → inc (inversel {x = x} i))
      (Coeq-elim-prop (λ _ → squash _ _) λ x i → inc (inverser {x = x} i))
      (Coeq-elim-prop (λ _ → squash _ _) λ x i → inc (idl {x = x} i))

  _/ᴳ_ : Group _
  _/ᴳ_ = G/H , Group-on-G/H

  incl : Groups.Hom Grp _/ᴳ_
  incl .fst = inc
  incl .snd .Group-hom.pres-⋆ x y = refl
```

Before we show that the kernel of the quotient map is isomorphic to the
subgroup we started with (and indeed, that this isomorphism commutes
with the respective, so that they determine the same subobject of $G$),
we must show that the relation $(x - y) \in H$ is an equivalence
relation; We can then appeal to [effectivity of quotients] to conclude
that, if $\id{inc}(x) = \id{inc}(y)$, then $(x - y) \in H$.

[effectivity of quotients]: Data.Set.Coequaliser.html#effecitivity

```agda
  private
    rel-sym : ∀ {x y} → rel x y → rel y x
    rel-sym h = subst (_∈ H) (inv-comm ∙ ap (_⋆ _) inv-inv) (has-inv h)

    rel-trans : ∀ {x y z} → rel x y → rel y z → rel x z
    rel-trans {x} {y} {z} h g = subst (_∈ H) p (has-⋆ h g) where
      p = (x — y) ⋆ (y — z)    ≡˘⟨ associative ⟩
          x ⋆ (y ⁻¹ ⋆ (y — z)) ≡⟨ ap (x ⋆_) associative ⟩
          x ⋆ ((y ⁻¹ ⋆ y) — z) ≡⟨ ap (x ⋆_) (ap (_⋆ _) inversel ∙ idl) ⟩
          x — z                ∎

  /ᴳ-effective : ∀ {x y} → Path G/H (inc x) (inc y) → rel x y
  /ᴳ-effective = equiv→inverse
    (effective (λ _ _ → H _ .is-tr) (rel-refl _) rel-trans rel-sym)
```

<!--
```agda
  private
    module Ker[incl] = Kernel (Ker incl)
    Ker-sg = Ker-subgroup incl
    H-sg = predicate→subgroup H has-rep
    H-g = H-sg .object ./-Obj.domain
```
-->

The two halves of the isomorphism are now very straightforward to
define: If we have $\id{inc}(x) = \id{inc}(0)$, then $x - 0 \in H$ by
effectivity, and $x \in H$ by the group laws. Conversely, if $x \in H$,
then $x - 0 \in H$, thus they are identified in the quotient. Thus, the
predicate $\id{inc}(x) = \id{inc}(0)$ recovers the subgroup $H$; And
(the total space of) that predicate is exactly the kernel of $\id{inc}$!

```agda
  Ker[incl]≅H-group : Ker[incl].ker Groups.≅ H-g
  Ker[incl]≅H-group = Groups.make-iso to from il ir where
    to : Groups.Hom _ _
    to .fst (x , p) = x , subst (_∈ H) (ap (_ ⋆_) inv-unit ∙ idr) x-0∈H where
      x-0∈H = /ᴳ-effective p
    to .snd .Group-hom.pres-⋆ _ _ = Σ-prop-path (λ _ → H _ .is-tr) refl

    from : Groups.Hom _ _
    from .fst (x , p) = x , quot (subst (_∈ H) (sym idr ∙ ap (_ ⋆_) (sym inv-unit)) p)
    from .snd .Group-hom.pres-⋆ _ _ = Σ-prop-path (λ _ → squash _ _) refl

    il = Forget-is-faithful $ funext λ x → Σ-prop-path (λ _ → H _ .is-tr) refl
    ir = Forget-is-faithful $ funext λ x → Σ-prop-path (λ _ → squash _ _) refl
```

To show that these are equal as subgroups of $G$, we must show that the
isomorphism above commutes with the inclusions; But this is immediate by
computation, so we can conclude: Every normal subgroup is a kernel.

```
  Ker[incl]≡H↪G : Ker-sg ≡ H-sg
  Ker[incl]≡H↪G = antisym ker≤H H≤ker where
    SubG = Subobjects (Groups ℓ) Groups-is-category Grp
    open Poset SubG
    open Groups._≅_ Ker[incl]≅H-group

    ker≤H : Ker-sg ≤ H-sg
    ker≤H ./-Hom.map = to
    ker≤H ./-Hom.commutes = Forget-is-faithful refl

    H≤ker : H-sg ≤ Ker-sg
    H≤ker ./-Hom.map = from
    H≤ker ./-Hom.commutes = Forget-is-faithful refl
```
