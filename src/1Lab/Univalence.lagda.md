```agda
open import 1Lab.Path.Groupoid
open import 1Lab.Type.Sigma
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.Univalence where
```

# Univalence

In Homotopy Type Theory, **univalence** is the principle stating that
[equivalent] types can be [identified]. When [the book] first came out,
there was no widely-accepted _computational_ interpretation of this
principle, so it was added to the theory as an axiom: the **univalence
axiom**.

[the book]: https://homotopytypetheory.org/book
[equivalent]: 1Lab.Equiv.html#_≃_
[identified]: 1Lab.Path.html#Path

Precisely, the axiom as presented in the book consists of the following
data (right under remark §2.10.4):

* A map which turns equivalences into identifications of types.
This map is called `ua`{.Agda}.

* A rule for eliminating identifications of types, by turning them into
equivalences: `path→equiv`{.Agda}

* The propositional computation rule, stating that transport along
`ua(f)` is identical to applying `f`: `uaβ`{.Agda}.

In the book, there is an extra postulated datum asserting that
`ua`{.Agda} is an inverse to `path→equiv`{.Agda}. This datum does not
have a name in this development, because it's proved in-line in the
construction of the term `univalence`{.Agda}.

The point of cubical type theory is to give these terms constructive
interpretations, i.e., make them definable in the theory, in terms of
constructions that have computational behaviour. Let's see how this is
done.

## Glue

To even _state_ univalence, we first have to make sure that the concept
of “paths between types” makes sense in the first place. In “Book HoTT”,
paths between types are a well-formed concept because the path type is
uniformly inductively defined for _everything_ --- including universes.
This is not the case in Cubical type theory, where for paths in $T$ to
be well-behaved, $T$ must [be _fibrant_].

[be _fibrant_]: 1Lab.Path.html#fibrant

Since there's no obvious choice for how to interpret `hcomp`{.Agda} in
`Type`{.Agda}, a fine solution is to make `hcomp`{.Agda} its own type
former. This is the approach taken by some Cubical type theories in the
[RedPRL school]. Univalence in those type theories is then achieved by
adding a type former, called `V`, which turns an equivalence into a
path.

[RedPRL school]: https://redprl.org/

[_equivalences_]: 1Lab.Equiv.html#is-equiv
[open box]: 1Lab.Path.html#transitivity

In [CCHM] --- and therefore Cubical Agda --- a different approach is
taken, which combines proving univalence with defining a fibrancy
structure for the universe. The core idea is to define a new type
former, `Glue`{.Agda}, which "glues" a [partial type], along an
equivalence, to a total type.

[CCHM]: https://arxiv.org/abs/1611.02108
[partial type]: 1Lab.Path.html#partial-elements

<!--
```agda
private
  variable
    ℓ ℓ' : Level

  primitive
    primGlue : (A : Type ℓ) {φ : I}
             → (T : Partial φ (Type ℓ')) → (e : PartialP φ (λ o → T o ≃ A))
             → Type ℓ'

    prim^glue : {A : Type ℓ} {φ : I}
              → {T : Partial φ (Type ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
              → PartialP φ T → A → primGlue A T e

    prim^unglue : {A : Type ℓ} {φ : I}
                → {T : Partial φ (Type ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
                → primGlue A T e → A

open import Agda.Builtin.Cubical.HCompU
open import 1Lab.Equiv.FromPath
```
-->

```agda
Glue : (A : Type ℓ)
     → {φ : I}
     → (Te : Partial φ (Σ[ T ∈ Type ℓ' ] (T ≃ A)))
     → Type ℓ'
```

The public interface of `Glue`{.Agda} demands a type $A$, called the
_base type_, a formula $\varphi$, and a [partial type] $T$ which is
equivalent to $A$. Since the equivalence is defined _inside_ the partial
element, it can also (potentially) vary over the interval, so in reality
we have a _family_ of partial types $T$ and a _family_ of partial
equivalences $T \simeq A$.

In the specific case where we set $\varphi = \neg i \lor i$, we can
illustrate `Glue A (T, f)` as the dashed line in the square diagram
below. The conceptual idea is that by "gluing" $T$ onto a totally
defined type, we get a type which [extends] $T$.

[extends]: 1Lab.Path.html#extensibility

~~~{.quiver}
\[\begin{tikzcd}
  {T(i0)} && {T(i1)} \\
  \\
  {A(i0)} && {A(i1)}
  \arrow[dashed, from=1-1, to=1-3]
  \arrow["A", from=3-1, to=3-3]
  \arrow["{f(i1)}"{description}, from=1-3, to=3-3]
  \arrow["{f(i0)}"{description}, from=1-1, to=3-1]
\end{tikzcd}\]
~~~

<!--
```agda
Glue A Te = primGlue A (λ x → Te x .fst) (λ x → Te x .snd)

unglue : {A : Type ℓ} (φ : I) {T : Partial φ (Type ℓ')}
         {e : PartialP φ (λ o → T o ≃ A)} → primGlue A T e → A
unglue φ = prim^unglue {φ = φ}
```
-->

[family of partial types]: 1Lab.Path.html#partial-elements

For `Glue`{.Agda} to extend $T$, we add a computation rule which could
be called a **boundary condition**, since it specifies how `Glue`{.Agda}
behaves on the boundaries of cubes. Concisely, when $\varphi = i1$, we
have that `Glue`{.Agda} evaluates to the partial type. This is exactly
what it means for `Glue`{.Agda} to extend $T$!

```agda
module _ {A B : Type} {e : A ≃ B} where
  private
    Glue-boundary : Glue B {i1} (λ x → A , e) ≡ A
    Glue-boundary i = A
```

Furthermore, since we can turn any family of paths into a family of
equivalences, we can use the `Glue`{.Agda} construct to implement
something with precisely the same interface as `hcomp`{.Agda} for
`Type`{.Agda}:

```agda
glue-hfill
  : ∀ {ℓ} φ (u : I → Partial φ (Type ℓ)) (u0 : Type ℓ [ φ ↦ u i0 ])
  → ∀ i → Type ℓ [ _ ↦ (λ { (i = i0) → outS u0
                          ; (φ = i1) → u i 1=1 }) ]
```

The type of `glue-hfill`{.Agda} is the same as that of `hfill`{.Agda},
but the type is stated much more verbosely --- so that we may define it
without previous reference to a `hcomp`{.Agda} analogue. Like
`hfill`{.Agda}, `glue-hfill`{.Agda} extends an open box of types to a
totally-defined cube. The type of `glue-hfill`{.Agda} expresses this in
terms of extensions: We have a path (that's the `∀ i →` binder) of
`Type`{.Agda}s which agrees with `outS u0` on the left endpoint, and
with `u` everywhere.

```agda
glue-hfill φ u u0 i = inS (
  Glue (outS u0) {φ = φ ∨ ~ i}
    λ { (φ = i1) → u i 1=1 , line→equiv (λ j → u (i ∧ ~ j) 1=1)
      ; (i = i0) → outS u0 , line→equiv (λ i → outS u0)
      })
```

In the case for  $i = \id{i0}$, we must glue $u0$ onto itself using the
identity equivalence. This guarantees that the boundary of the stated
type for `glue-hfill`{.Agda} is satisfied. However, since different
faces of partial elements must agree where they are defined, we can not
use the identity equivalence directly, since `line→equiv refl` is not
definitionally the identity equivalence.

When $\varphi = \id{\phi}$, hence where $u$ is defined, we glue the
endpoint $u$ onto $u0$ using the equivalence generated by the path
provided by $u$ itself! It's a family of partial paths, after all, and
that can be turned into a family of partial equivalences.

To show that `glue-hfill`{.Agda} expresses the fibrancy structure of the
universe, we prove a theorem that says anything with the same interface
as `hfill`{.Agda} must agree with `hcomp`{.Agda} on `i1`{.Agda}, and
from this conclude that `hcomp`{.Agda} on `Type`{.Agda} agrees with the
definition of `glue-hfill`{.Agda}.

```agda
hcomp-unique : ∀ {ℓ} {A : Type ℓ} {φ}
               (u : I → Partial φ A)
               (u0 : A [ φ ↦ u i0 ])
             → (h2 : ∀ i → A [ _ ↦ (λ { (i = i0) → outS u0
                                      ; (φ = i1) → u i 1=1 }) ])
             → hcomp u (outS u0) ≡ outS (h2 i1)
hcomp-unique {φ = φ} u u0 h2 i =
  hcomp (λ k → λ { (φ = i1) → u k 1=1
                 ; (i = i1) → outS (h2 k) })
        (outS u0)
```

Using `hcomp-unique`{.Agda} and `glue-hfill`{.Agda} together, we get a
internal characterisation of the fibrancy structure of the universe.
While `hcomp-unique`{.Agda} may appear surprising, it is essentially a
generalisation of the uniqueness of path compositions: Any open box has
a contractible space of fillers.

```agda
hcomp≡Glue : ∀ {ℓ} {φ} (u : I → Partial φ (Type ℓ)) (u0 : Type ℓ [ φ ↦ u i0 ])
           → hcomp u (outS u0)
           ≡ Glue (outS u0)
              (λ { (φ = i1) → u i1 1=1 , line→equiv (λ j → u (~ j) 1=1) })
hcomp≡Glue u u0 = hcomp-unique u u0 (glue-hfill _ u u0)
```

## Paths from Glue

Since `Glue`{.Agda} generalises `hcomp`{.Agda} by allowing a partial
equivalence as its “tube”, rather than a partial path, it allows us to
turn any equivalence into a path, using a sort of "trick": We consider
the _line_ with endpoints $A$ and $B$ as an open cube to be filled. A
filler for this line is exactly a path $A \equiv B$. Since `Glue`{.Agda}
fills open boxes of types using equivalences, this path exists!

```agda
ua : {A B : Type ℓ} → A ≃ B → A ≡ B
ua {A = A} {B} eqv i = Glue B λ { (i = i0) → A , eqv
                                ; (i = i1) → B , _ , id-equiv
                                }
```

Semantically, the explanation of `ua`{.Agda} as completing a partial
line is sufficient. But we can also ask ourselves: Why does this
definition go through, _syntactically_? Because of the boundary
condition for Glue: when `i = i0`, the whole thing evaluates to `A`,
meaning that the left endpoint of the path is correct. The same thing
happens with the right endpoint.

The action of [transporting] along `ua(f)` can be described by chasing
an element around the diagram that illustrates Glue in the $\varphi = i
\lor \neg i$ case, specialising to `ua`{.Agda}. Keep in mind that, since
the right face of the diagram "points in the wrong direction", it must
be inverted. However, the inverse of the identity equivalence is the
identity equivalence, so nothing changes (for this example).

[transporting]: 1Lab.Path.html

<figure>
~~~{.quiver}
\[\begin{tikzcd}
  A && B \\
  \\
  B && B
  \arrow["{\id{refl}}"', from=3-1, to=3-3]
  \arrow["f"', "\text{\rotatebox[origin=c]{90}{$\sim$}}", from=1-1, to=3-1]
  \arrow["{\id{id}}", "\text{\rotatebox[origin=c]{270}{$\sim$}}"', from=1-3, to=3-3]
  \arrow["{\id{ua}(f)}", dashed, from=1-1, to=1-3]
\end{tikzcd}\]
~~~
</figure>

1. The action that corresponds to the left face of the diagram is to
apply the underlying function of `f`. This contributes the `f .fst x`
part of the `uaβ`{.Agda} term below.

[a pair]: 1Lab.Equiv.html#_≃_

2. For the bottom face, we have a path rather than an equivalence, so we
must `transport`{.Agda} along it. In this case, the path is the
reflexivity on `B`, but in a more general `Glue`{.Agda} construction, it
might be a non-trivial path.

  To compensate for this extra transport, we use `coe1→i`{.Agda}, which
  connects `f .fst x` and `transport (λ i → B) (f .fst x)`.

3. Finally, we apply the inverse of the identity equivalence,
corresponding to the right face in the diagram. This immediately
computes away, and thus contributes nothing to the `uaβ`{.Agda} path.

```agda
uaβ : {A B : Type ℓ} (f : A ≃ B) (x : A) → transport (ua f) x ≡ f .fst x
uaβ {A = A} {B} f x i = coe1→i (λ _ → B) i (f .fst x)
```

Since `ua`{.Agda} is a map that turns equivalences into paths, we can
compose it with a function that turns [isomorphisms] into equivalences
to get the map `Iso→Path`{.Agda}.

[isomorphisms]: 1Lab.Equiv.html#Iso

```agda
Iso→Path : {A B : Type ℓ} → Iso A B → A ≡ B
Iso→Path (f , iiso) = ua (f , is-iso→is-equiv iiso)
```

## Paths over ua

The introduction and elimination forms for `Glue`{.Agda} can be
specialised to the case of `ua`{.Agda}, leading to the definitions of
`ua-glue`{.Agda} and `ua-unglue`{.Agda} below. Their types are written
in terms of interval variables and [extensions], rather than using
`Path`{.Agda}s, because these typings make the structure of
`Glue`{.Agda} more explicit.

[extensions]: 1Lab.Path.html#extensibility

The first, `ua-unglue`{.Agda}, tells us that if we have some `x : ua e
i` (varying over an interval variable `i`), then we have an element of
`B` which agrees with `e .fst x` on the left and with `x` on the right.

```agda
ua-unglue : ∀ {A B : Type ℓ} (e : A ≃ B) (i : I) (x : ua e i)
            → B [ _ ↦ (λ { (i = i0) → e .fst x
                         ; (i = i1) → x }) ]
ua-unglue e i x = inS (unglue (i ∨ ~ i) x)
```

We can factor the interval variable out, to get a type in terms of
`PathP`{.Agda}, leading to an explanation of `ua-unglue` without
mentioning extensions: A path `x ≡ y` over `ua e` induces a path `e .fst
x ≡ y`.

```agda
ua-pathp→path : ∀ {A B : Type ℓ} (e : A ≃ B) {x : A} {y : B}
              → PathP (λ i → ua e i) x y
              → e .fst x ≡ y
ua-pathp→path e p i = outS (ua-unglue e i (p i))
```

In the other direction, we have `ua-glue`{.Agda}, which expresses that a
path `e .fst x ≡ y` implies that `x ≡ y` over `ua e`. For the type of
`ua-glue`{.Agda}, suppose that we have a partial element $x$ defined on
the left endpoint of the interval, together with an extension $y$ of
$e(x)$ where $x$ is defined. What `ua-glue`{.Agda} expresses is that we
can complete this to a path in $\id{ua}(e)$, which agrees with $x$ and
$y$ where these are defined.

```agda
ua-glue : ∀ {A B : Type ℓ} (e : A ≃ B) (i : I)
            (x : Partial (~ i) A)
            (y : B [ _ ↦ (λ { (i = i0) → e .fst (x 1=1) }) ])
          → ua e i [ _ ↦ (λ { (i = i0) → x 1=1
                            ; (i = i1) → outS y
                            }) ]
ua-glue e i x y = inS (prim^glue {φ = i ∨ ~ i}
                                 (λ { (i = i0) → x 1=1
                                    ; (i = i1) → outS y })
                                 (outS y))
```

Observe that, since $y$ is partially in the image of $x$, this
essentially constrains $x$ to be a “partial preimage” of $y$ under the
equivalence $e$. Factoring in the type of the interval, we get the
promised map between dependent paths over `ua`{.Agda} and paths in B.

```agda
path→ua-pathp : ∀ {A B : Type ℓ} (e : A ≃ B) {x : A} {y : B}
              → e .fst x ≡ y
              → PathP (λ i → ua e i) x y
path→ua-pathp e {x = x} p i = outS (ua-glue e i (λ { (i = i0) → x }) (inS (p i)))
```

The "pathp to path" versions of the above lemmas are definitionally
inverses, so they provide a characterisation of `PathP (ua f)` in terms
of non-dependent paths.

```agda
ua-pathp≃path : ∀ {A B : Type ℓ} (e : A ≃ B) {x : A} {y : B}
              → (e .fst x ≡ y) ≃ (PathP (λ i → ua e i) x y)
ua-pathp≃path eqv .fst = path→ua-pathp eqv
ua-pathp≃path eqv .snd .is-eqv y .centre = strict-fibres (ua-pathp→path eqv) y .fst
ua-pathp≃path eqv .snd .is-eqv y .paths = strict-fibres (ua-pathp→path eqv) y .snd
```

# The “axiom”

The actual “univalence axiom”, as stated in the HoTT book, says that the
canonical map `A ≡ B`, defined using `J`{.Agda}, is an equivalence. This
map is `id→equiv`{.Agda}, defined right above. In more intuitive terms,
it's "casting" the identity equivalence `A ≃ A` along a proof that `A ≡
B` to get an equivalence `A ≃ B`.

```agda
module _ where private
  id→equiv : {A B : Type ℓ} → A ≡ B → A ≃ B
  id→equiv {A = A} {B} = J (λ x _ → A ≃ x) (_ , id-equiv)

  id→equiv-refl : {A : Type ℓ} → id→equiv (λ i → A) ≡ (_ , id-equiv)
  id→equiv-refl {A = A} = J-refl (λ x _ → A ≃ x) (_ , id-equiv)
```

However, because of efficiency concerns (Agda _is_ a programming
language, after all), instead of using `id→equiv`{.Agda} defined using
J, we use `path→equiv`{.Agda}, which is [defined in an auxilliary
module](1Lab.Equiv.FromPath.html).

```agda
path→equiv : {A B : Type ℓ} → A ≡ B → A ≃ B
path→equiv p = line→equiv (λ i → p i)
```

Since identity of equivalences is determined by identity of their
underlying functions, to show that `path→equiv`{.Agda} of `refl`{.Agda}
is the identity equivalence, we use `coe1→i`{.Agda} to show that
`transport`{.Agda} by `refl`{.Agda} is the identity.

```agda
path→equiv-refl : {A : Type ℓ} → path→equiv (refl {x = A}) ≡ (id , id-equiv)
path→equiv-refl {A = A} =
  Σ-path (λ i x → coe1→i (λ i → A) i x)
         (is-prop→pathp (λ i → is-equiv-is-prop _) _ _)
```

For the other direction, we must show that `ua`{.Agda} of
`id-equiv`{.Agda} is `refl`{.Agda}. We can do this quite efficiently
using `Glue`{.Agda}. Since this is a path between paths, we have two
interval variables.

```agda
ua-id-equiv : {A : Type ℓ} → ua (_ , id-equiv {A = A}) ≡ refl
ua-id-equiv {A = A} i j = Glue A {φ = i ∨ ~ j ∨ j} (λ _ → A , _ , id-equiv)
```

We can then prove that the map `path→equiv`{.Agda} is an isomorphism,
hence an equivalence. It's very useful to have explicit names for the
proofs that `path→equiv`{.Agda} and `ua`{.Agda} are equivalences
without referring to components of `Path≃Equiv`{.Agda}, so we
introduce names for them as well.

```agda
Path≃Equiv   : {A B : Type ℓ} → Iso (A ≡ B) (A ≃ B)
univalence   : {A B : Type ℓ} → is-equiv (path→equiv {A = A} {B})
univalence⁻¹ : {A B : Type ℓ} → is-equiv (ua {A = A} {B})

Path≃Equiv {A = A} {B = B} = path→equiv , iiso where
  iiso : is-iso path→equiv
  is-iso.inv iiso = ua
```

We show that `path→equiv` inverts `ua`{.Agda}, which means proving that
one can recover the original equivalence from the generated path.
Because of the computational nature of Cubical Agda, all we have to do
is apply `uaβ`{.Agda}:

```agda
  is-iso.rinv iiso (f , is-eqv) =
    Σ-path (funext (uaβ (f , is-eqv))) (is-equiv-is-prop f _ _)
```

For the other direction, we use [path induction] to reduce the problem
from showing that `ua`{.Agda} inverts `path→equiv`{.Agda} for an
arbitrary path (which is hard) to showing that `path→equiv`{.Agda}
takes `refl`{.Agda} to the identity equivalence
(`path→equiv-refl`{.Agda}), and that `ua`{.Agda} takes the identity
equivalence to `refl`{.Agda} (`ua-id-equiv`{.Agda}).

[path induction]: 1Lab.Path.html#J

```agda
  is-iso.linv iiso =
    J (λ _ p → ua (path→equiv p) ≡ p)
      (ap ua path→equiv-refl ∙ ua-id-equiv)

univalence {A = A} {B} = is-iso→is-equiv (Path≃Equiv .snd)
univalence⁻¹ {A = A} {B} = is-iso→is-equiv (is-iso.inverse (Path≃Equiv .snd))
```

In some situations, it is helpful to have a proof that
`path→equiv`{.Agda} followed by `an adjustment of levels`{.Agda
ident=Lift} is still an equivalence:

```agda
univalence-lift : {A B : Type ℓ} → is-equiv (λ e → lift (path→equiv {A = A} {B} e))
univalence-lift {ℓ = ℓ} = is-iso→is-equiv morp where
  morp : is-iso (λ e → lift {ℓ = lsuc ℓ} (path→equiv e))
  morp .is-iso.inv x = ua (x .Lift.lower)
  morp .is-iso.rinv x =
    lift (path→equiv (ua (x .Lift.lower))) ≡⟨ ap lift (Path≃Equiv .snd .is-iso.rinv _) ⟩
    x                                      ∎
  morp .is-iso.linv x = Path≃Equiv .snd .is-iso.linv _
```

## Equivalence Induction

One useful consequence of $(A \equiv B) \simeq (A \simeq B)$[^2] is that
the type of _equivalences_ satisfies [the same induction principle] as
the type of _identifications_. By analogy with how path induction can be
characterised as contractibility of singletons and transport,
“equivalence induction” can be characterised as transport and
contractibility of _singletons up to equivalence_:

[the same induction principle]: 1Lab.Path.html#J

```agda
Equiv-is-contr : ∀ {ℓ} (A : Type ℓ) → is-contr (Σ[ B ∈ Type ℓ ] A ≃ B)
is-contr.centre (Equiv-is-contr A)            = A , _ , id-equiv
is-contr.paths (Equiv-is-contr A) (B , A≃B) i = ua A≃B i , p i , q i where
  p : PathP (λ i → A → ua A≃B i) id (A≃B .fst)
  p i x = outS (ua-glue A≃B i (λ { (i = i0) → x }) (inS (A≃B .fst x)))

  q : PathP (λ i → is-equiv (p i)) id-equiv (A≃B .snd)
  q = is-prop→pathp (λ i → is-equiv-is-prop (p i)) _ _
```

Combining `Equiv-is-contr`{.Agda} with `subst`{.Agda}, we get an induction
principle for the type of equivalences based at $A$: To prove $P(B,e)$
for any $e : A \simeq B$, it suffices to consider the case where $B$ is
$A$ and $e$ is the identity equivalence.

```agda
EquivJ : ∀ {ℓ ℓ'} {A : Type ℓ}
       → (P : (B : Type ℓ) → A ≃ B → Type ℓ')
       → P A (_ , id-equiv)
       → {B : Type ℓ} (e : A ≃ B)
       → P B e
EquivJ P pid eqv =
  subst (λ e → P (e .fst) (e .snd)) (Equiv-is-contr _ .is-contr.paths (_ , eqv)) pid
```

[^2]: Not the fundamental theorem of engineering!

Equivalence induction simplifies the proofs of many properties about
equivalences. For example, if $f$ is an equivalence, then so is its
`action on paths`{.Agda ident=ap} $\id{ap}(f)$.

```agda
is-equiv→is-embedding : ∀ {ℓ} {A B : Type ℓ}
                      → (f : A → B) → is-equiv f
                      → {x y : A}
                      → is-equiv (ap f {x = x} {y = y})
is-equiv→is-embedding f eqv =
  EquivJ (λ B e → is-equiv (ap (e .fst))) id-equiv (f , eqv)
```

The proof can be rendered in English roughly as follows:

> Suppose $f : A \to B$ `is an equivalence`{.Agda ident=is-equiv}. We
want to show that, for any choice of $x, y : A$, the map
$\id{ap}(f)_{x,y} : x \equiv y \to f(x) \equiv f(y)$ is an equivalence.
>
> By `induction`{.Agda ident=EquivJ}, it suffices to cover the case
where $B$ is $A$, and $f$ is the identity function.
>
> But then, we have that $\id{ap}(\id{id})$ is [definitionally
equal](1Lab.Path.html#ap-id) to $\id{id}$, which is known to be `an
equivalence`{.Agda ident=id-equiv}. <span
class=qed>$\blacksquare$</span>

## Object Classifiers

In category theory, the idea of _classifiers_ (or _classifying objects_)
often comes up when categories applied to the study of logic. For
example, any [elementary topos] has a _[subobject classifier]_: an
object $\Omega$ such that maps $B \to \Omega$ corresponds to maps $A \to
B$ with propositional fibres (equivalently, inclusions $A
\hookrightarrow B$). In higher categorical analyses of logic,
classifying objects exist for more maps: an elementary
**2**-topos has a [discrete object classifier], which classify maps with
_discrete_ fibres.

[elementary topos]: https://ncatlab.org/nlab/show/topos#ElementaryTopos
[subobject classifier]: https://ncatlab.org/nlab/show/subobject+classifier
[discrete object classifier]: https://ncatlab.org/nlab/show/discrete+object+classifier

Since a $(1,1)$-topos has classifiers for maps with $(-1)$-truncated
fibres, and a $(2,1)$-topos has classifiers for maps with $0$-truncated
fibres, one might expect that an [$\io$-topos] would have
classifiers for maps with fibres that are not truncated at all. This is
indeed the case! In HoTT, this fact is internalised using the univalent
universes, and we can prove that univalent universes are [_object
classifiers_].

[$\io$-topos]: https://ncatlab.org/nlab/show/(infinity,1)-topos
[_object classifiers_]: https://ncatlab.org/nlab/show/object+classifier

<!--
```agda
private variable
  A B E : Type ℓ
open is-iso
```
-->

As an intermediate step, we prove that the value $B(a)$ of a type family
$B$ at a point $a$ is equivalent to the fibre of $\id{fst} : \Sigma_{(x
: A)}B(x) \to A$ over $a$. The proof follows from the De Morgan
structure on the interval, and the “spread” operation `coe1→i`{.Agda}.

```agda
-- HoTT book lemma 4.8.1
Fibre-equiv : (B : A → Type ℓ') (a : A)
            → fibre (fst {B = B}) a ≃ B a
Fibre-equiv B a = Iso→Equiv isom where
  isom : Iso _ _
  isom .fst ((x , y) , p) = subst B p y
  isom .snd .inv x        = (a , x) , refl
  isom .snd .rinv x i     = coe1→i (λ _ → B a) i x
  isom .snd .linv ((x , y) , p) i =
    (p (~ i) , coe1→i (λ j → B (p (~ i ∧ ~ j))) i y) , λ j → p (~ i ∨ j)
```

Another fact from homotopy theory that we can import into homotopy
_type_ theory is that any map is equivalent to a fibration. More
specifically, given a map $p : E \to B$, the total space $E$ is
equivalent to the dependent sum of the fibres. The theorems
`Total-equiv`{.Agda} and `Fibre-equiv`{.Agda} are what justify referring
to `Σ`{.Agda} the "total space" of a type family.

```agda
Total-equiv : (p : E → B) → E ≃ Σ (fibre p)
Total-equiv p = Iso→Equiv isom where
  isom : Iso _ (Σ (fibre p))
  isom .fst x                   = p x , x , refl
  isom .snd .inv (_ , x , _)    = x
  isom .snd .rinv (b , x , q) i = q i , x , λ j → q (i ∧ j)
  isom .snd .linv x             = refl
```

Putting these together, we get the promised theorem: The space of maps
$B \to \ty$ is equivalent to the space of fibrations with base
space $B$ and variable total space $E$, $\Sigma_{(E : \ty)}
(E \to B)$. If we allow $E$ and $B$ to live in different universes, then
the maps are classified by the biggest universe in which they both fit,
namely `Type (ℓ ⊔ ℓ')`. Note that the proof of `Fibration-equiv`{.Agda}
makes fundamental use of `ua`{.Agda}, to construct the witnesses that
taking fibres and taking total spaces are inverses. Without `ua`{.Agda},
we could only get an "isomorphism-up-to-equivalence" of types.

```agda
Fibration-equiv : ∀ {ℓ ℓ'} {B : Type ℓ}
                → (Σ[ E ∈ Type (ℓ ⊔ ℓ') ] (E → B))
                ≃ (B → Type (ℓ ⊔ ℓ'))
Fibration-equiv {B = B} = Iso→Equiv isom where
  isom : Iso (Σ[ E ∈ Type _ ] (E → B)) (B → Type _)
  isom .fst (E , p)       = fibre p
  isom .snd .inv p⁻¹      = Σ p⁻¹ , fst
  isom .snd .rinv prep i x = ua (Fibre-equiv prep x) i
  isom .snd .linv (E , p) i
    = ua e (~ i) , λ x → fst (outS (ua-unglue e (~ i) x))
    where e = Total-equiv p
```

To solidify the explanation that object classifiers generalise the
$(n-2)$-truncated object classifiers you would find in a $(n,1)$-topos,
we prove that any class of maps described by a property $P$ which holds
of all of its fibres (or even _structure_ on all of its fibres!) has a
classifying object --- the total space $\Sigma P$.

For instance, if we take $P$ to be the property of `being a
proposition`{.Agda ident=is-prop}, this theorem tells us that `Σ is-prop`
classifies _subobjects_. With the slight caveat that `Σ is-prop` is not
closed under impredicative quantification, this corresponds exactly to
the notion of subobject classifier in a $(1,1)$-topos, since the maps
with propositional fibres are precisely the injective maps.

<!--
```
_ = is-prop
```
-->

Since the type of "maps into B with variable domain and P fibres" has a
very unwieldy description --- both in words or in Agda syntax --- we
abbreviate it by $\ell /_{[P]} B$. The notation is meant to evoke the
idea of a slice category: The objects of $C/c$ are objects of the
category $C$ equipped with choices of maps into $c$. Similarly, the
objects of $\ell/_{[P]}B$ are objects of the universe $\ty\
\ell$, with a choice of map $f$ into $B$, such that $P$ holds for all
the fibres of $f$.

```agda
_/[_]_ : ∀ {ℓ' ℓ''} (ℓ : Level) → (Type (ℓ ⊔ ℓ') → Type ℓ'') → Type ℓ' → Type _
_/[_]_ {ℓ} ℓ' P B =
  Σ λ (A : Type (ℓ ⊔ ℓ')) →
  Σ λ (f : A → B) →
  (x : B) → P (fibre f x)
```

The proof that the slice $\ell /_{[P]} B$ is classified by $\Sigma P$
follows from elementary properties of $\Sigma$ types (namely:
`reassociation`{.Agda ident=Σ-assoc}, `distributivity`{.Agda
ident=Σ-Π-distrib} of $\Sigma$ over $\Pi$), and the classification
theorem `Fibration-equiv`{.Agda}. Really, the most complicated part of
this proof is rearranging the nested sum and product types to a form to
which we can apply `Fibration-equiv`{.Agda}.

```agda
Map-classifier
  : ∀ {ℓ ℓ' ℓ''} {B : Type ℓ'} (P : Type (ℓ ⊔ ℓ') → Type ℓ'')
  → (ℓ /[ P ] B) ≃ (B → Σ P)
Map-classifier {ℓ = ℓ} {B = B} P =
  (Σ λ A → Σ λ f → (x : B) → P (fibre f x))     ≃⟨ Σ-assoc ⟩
  (Σ λ { (x , f) → (x : B) → P (fibre f x) })   ≃⟨ Σ-ap-fst (Fibration-equiv {ℓ' = ℓ}) ⟩
  (Σ λ A → (x : B) → P (A x))                   ≃⟨ Σ-Π-distrib e⁻¹ ⟩
  (B → Σ P)                                     ≃∎
```

<!--
```agda
ua∙ : ∀ {A B C : Type ℓ} {f : A ≃ B} {g : B ≃ C}
    → ua (f ∙e g) ≡ ua f ∙ ua g
ua∙ {C = C} {f = f} {g} =
  EquivJ
    (λ B eq → (g : B ≃ C) → ua (eq ∙e g) ≡ ua eq ∙ ua g)
    (λ g → ap ua (Σ-prop-path is-equiv-is-prop (refl {x = g .fst}))
        ·· sym (∙-id-l (ua g))
        ·· ap₂ _∙_ (sym ua-id-equiv) refl)
    f g

ua→ : ∀ {ℓ ℓ'} {A₀ A₁ : Type ℓ} {e : A₀ ≃ A₁} {B : (i : I) → Type ℓ'}
  {f₀ : A₀ → B i0} {f₁ : A₁ → B i1}
  → ((a : A₀) → PathP B (f₀ a) (f₁ (e .fst a)))
  → PathP (λ i → ua e i → B i) f₀ f₁
ua→ {e = e} {f₀ = f₀} {f₁} h i a =
  hcomp
    (λ j → λ
      { (i = i0) → f₀ a
      ; (i = i1) → f₁ (lem a j)
      })
    (h (transp (λ j → ua e (~ j ∧ i)) (~ i) a) i)
  where
  lem : ∀ a₁ → e .fst (transport (sym (ua e)) a₁) ≡ a₁
  lem a₁ = equiv→section (e .snd) _ ∙ transport-refl _

ua→2 : ∀ {ℓ ℓ' ℓ''} {A₀ A₁ : Type ℓ} {e₁ : A₀ ≃ A₁}
  {B₀ B₁ : Type ℓ'} {e₂ : B₀ ≃ B₁}
  {C : (i : I) → Type ℓ''}
  {f₀ : A₀ → B₀ → C i0} {f₁ : A₁ → B₁ → C i1}
  → (∀ a b → PathP C (f₀ a b) (f₁ (e₁ .fst a) (e₂ .fst b)))
  → PathP (λ i → ua e₁ i → ua e₂ i → C i) f₀ f₁
ua→2 h = ua→ (ua→ ∘ h)

transport-∙ : ∀ {ℓ} {A B C : Type ℓ}
            → (p : A ≡ B) (q : B ≡ C) (u : A)
            → transport (p ∙ q) u ≡ transport q (transport p u)
transport-∙ p q x i =
  transport (∙-filler' p q (~ i)) (transport-filler-ext p i x)

subst-∙ : ∀ {ℓ ℓ′} {A : Type ℓ} → (B : A → Type ℓ′)
        → {x y z : A} (p : x ≡ y) (q : y ≡ z) (u : B x)
        → subst B (p ∙ q) u ≡ subst B q (subst B p u)
subst-∙ B p q Bx i =
  transport (ap B (∙-filler' p q (~ i))) (transport-filler-ext (ap B p) i Bx)

sym-ua : ∀ {ℓ} {A B : Type ℓ} (e : A ≃ B) → sym (ua e) ≡ ua (e e⁻¹)
sym-ua = EquivJ (λ B e → sym (ua e) ≡ ua (e e⁻¹))
  (ap sym ua-id-equiv ∙ sym (ap ua (Σ-prop-path is-equiv-is-prop refl) ∙ ua-id-equiv))
```
-->
