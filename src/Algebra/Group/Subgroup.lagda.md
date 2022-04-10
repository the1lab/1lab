```agda
open import Cat.Diagram.Equaliser.Kernel

open import Algebra.Group.Cat.FinitelyComplete
open import Algebra.Group.Cat.Base
open import Algebra.Prelude
open import Algebra.Group

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
by equipping the `image`{.Agda} with a group structure inherited from
$B$. More concretely, we can describe the elements of $\im f$ as the
"mere fibres" of $f$: They consist of a point $y : B$, together with
(the truncation of) a fibre of $f$ over $y$. We multiply $x$ (in the
fibre over $a$) with $y$ (in the fibre over $b$), giving the element
$xy$ in the fibre over $ab$.

[image]: Cat.Diagram.Image.html

<!--
```agda
module _ {ℓ} {A B : Group ℓ} (f : Groups.Hom A B) where
  private
    module A = Group-on (A .snd)
    module B = Group-on (B .snd)
    module f = Group-hom (f .snd)

    T : Type ℓ
    T = image (f .fst)

    Tpath : {x y : T} → x .fst ≡ y .fst → x ≡ y
    Tpath {x} {y} p = Σ-prop-path (λ _ → squash) p

    abstract
      Tset : is-set T
      Tset = Σ-is-hlevel 2 B.has-is-set (λ _ → is-prop→is-set squash)

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
  A/ker[_] : Group ℓ
  A/ker[_] = T , grp where
    unit : T
    unit = B.unit , inc (A.unit , f.pres-id)

    inv : T → T
    inv (x , p) = x B.⁻¹ ,
      ∥-∥-map (λ { (y , p) → y A.⁻¹ , f.pres-inv _ ∙ ap B._⁻¹ p }) p

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
             → e' (x .fst) F.⋆ e' (y .fst) F.⁻¹ ≡ F.unit
      const′ (y , q) (z , r) =
        e' y F.⋆ (e' z) F.⁻¹ ≡˘⟨ ap (e' y F.⋆_) (e'.pres-inv _) ⟩
        e' y F.⋆ e' (z A.⁻¹) ≡˘⟨ e'.pres-⋆ _ _ ⟩
        e' (y A.⋆ z A.⁻¹)    ≡⟨ happly (sym (ap fst p)) (y A.⋆ z A.⁻¹ , aux) ⟩
        e' A.unit            ≡⟨ e'.pres-id ⟩
        F.unit               ∎
        where
```

This assumption allows us to reduce "show that $e'$ is constant on a
specific subset" to "show that $f(y - z) = 0$ when $f(y) = f(z) = x$";
But that's just algebra, hence uninteresting:

```agda
          aux : f .fst (y A.⋆ z A.⁻¹) ≡ B.unit
          aux =
            f .fst (y A.⋆ z A.⁻¹)        ≡⟨ f.pres-⋆ _ _ ⟩
            f .fst y B.⋆ f .fst (z A.⁻¹) ≡⟨ ap (_ B.⋆_) (f.pres-inv _) ⟩
            f .fst y B.⋆ (f .fst z) B.⁻¹ ≡⟨ ap₂ B._⋆_ q (ap B.inverse r) ⟩
            x B.⋆ x B.⁻¹                 ≡⟨ B.inverser ⟩
            B.unit                       ∎

      const : ∀ (x y : fibre (f .fst) x) → (e' (x .fst)) ≡ (e' (y .fst))
      const a b = F.zero-diff→≡ (const′ a b)
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
