```agda
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
[equivalent]: agda://1Lab.Equiv#_≃_
[identified]: agda://1Lab.Path#Path

Precisely, the axiom as presented in the book consists of the following
data (right under remark §2.10.4):

* A map which turns equivalences into propositional equalities of type.
This map is called `ua`{.Agda}.

* A rule for eliminating equalities of types, by turning them into
equivalences: `pathToEquiv`{.Agda}

* The propositional computation rule, stating that transport along
`ua(f)` is equal to applying `f`: `uaβ`{.Agda}.

In the book, there is an extra postulated datum asserting that
`ua`{.Agda} is an inverse to `pathToEquiv`{.Agda}. This datum does not
have a name in this development, because it's proved in-line in the
construction of the term `univalence`{.Agda}.

The point of cubical type theory is to give these terms constructive
interpretations, i.e., make them definable in the theory, in terms of
constructions that have computational behaviour. Let's see how this is
done.

## Cubically

The idea is that if you have an [open box] in `Type`{.Agda}, it's possible
to replace some faces with [_equivalences_](agda://1Lab.Equiv#isEquiv)
rather than _paths_ and still have everything work out. For example, we
can extend the canonical equivalence between unary and binary natural
numbers to a path in the universe:

[open box]: 1Lab.Path.html#transitivity

<figure>

~~~{.quiver .short-2}
\[\begin{tikzcd}
  {\mathrm{Nat}} && {\mathrm{Bin}}
  \arrow["\simeq", from=1-1, to=1-3]
\end{tikzcd}\]
~~~

<figcaption>
Even though this diagram indicates a _path_, the arrow is marked with
$\simeq$, to indicate that it comes from an equivalence.
</figcaption>

</figure>

In the one-dimensional case, this corresponds to having a constant
`ua`{.Agda} which turns an equivalence into a
[path](agda://1Lab.Path#Path). If this function additionally satisfies
"[transport](agda://1Lab.Path#transport) along ua(f) is the same as
applying f" (`uaβ`{.Agda}), then this function can be shown to be an
inverse to the map `pathToEquiv`{.Agda}.


[an internal Agda module]: Agda.Builtin.Cubical.HCompU.html

<!--
```
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

Since in Cubical Agda, things are naturally higher-dimensional, only
having a term `ua`{.Agda} wouldn't do! Instead, we introduce a new _type
former_, **Glue**, which, unlike the type formers like `Type`{.Agda},
`Σ`{.Agda}, and dependent functions, has **computational content**.

```agda
Glue : (A : Type ℓ)
     → {φ : I}
     → (Te : Partial φ (Σ[ T ∈ Type ℓ' ] (T ≃ A)))
     → Type ℓ'
```

To make **Glue**, you need:

- A type `A`, called the _base type_. Since this is a term of type
`Type`{.Agda}, it can depend on interval variables which are in-scope,
so in reality we have a $n$-cube of base types.

- An interval formula `φ`, and a _[family of partial types]_ $(T, e)$,
defined along `φ`. These must all be equivalent to the base type, by the
equivalences $e$. The idea is that we are extending a partial cube `Te`
to one which is [totally defined], by adding "enough equivalences" to
complete the square.

[totally defined]: 1Lab.Path.html#extensibility

In the case where we set $\phi = i \lor \neg i$, we can illustrate `Glue
A (T, f)` as the dashed line in the diagram below. The equivalences $f$
provide us _exactly_ the right amount of data to Glue $T$ onto $A$ and
get something total.

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
```
Glue A Te = primGlue A (λ x → Te x .fst) (λ x → Te x .snd)

unglue : {A : Type ℓ} (φ : I) {T : Partial φ (Type ℓ')}
         {e : PartialP φ (λ o → T o ≃ A)} → primGlue A T e → A
unglue φ = prim^unglue {φ = φ}
```
-->

[family of partial types]: 1Lab.Path.html#partial-elements

The point of `Glue`{.Agda} is that it satisfies a computation rule which
could be called a **_boundary condition_**, since it specifies how
`Glue`{.Agda} behaves on the boundaries of cubes. When $\phi = i1$, we
have that `Glue`{.Agda} evaluates to the partial type:

```agda
module _ {A B : Type} {e : A ≃ B} where
  private
    Glue-boundary : Glue B {i1} (λ x → A , e) ≡ A
    Glue-boundary i = A
```

Using Glue, we can turn any equivalence into a path:

```agda
ua : {A B : Type ℓ} → A ≃ B → A ≡ B
ua {A = A} {B} eqv i = Glue B λ { (i = i0) → A , eqv
                                ; (i = i1) → B , _ , idEquiv
                                }
```

Why does this definition go through? Because of the boundary condition
for Glue! When `i = i0`, the whole thing evaluates to `A`, meaning that
the left endpoint of the path is correct. The same thing happens with
the right endpoint.

The action of [transporting] along `ua(f)` can be described exactly by
chasing an element around the diagram that illustrates Glue in the $\phi
= i \lor \neg i$ case, specialising to `ua`{.Agda}, remembering that we
can invert equivalences to make this possible.

[transporting]: agda://1Lab.Path#transport

<figure>
~~~{.quiver}
\[\begin{tikzcd}
  A && B \\
  \\
  B && B
  \arrow["{\mathrm{refl}}"', from=3-1, to=3-3]
  \arrow["f"', "\text{\rotatebox[origin=c]{90}{$\sim$}}", from=1-1, to=3-1]
  \arrow["{\mathrm{id}}", "\text{\rotatebox[origin=c]{270}{$\sim$}}"', from=1-3, to=3-3]
  \arrow["{\mathrm{ua}(f)}", dashed, from=1-1, to=1-3]
\end{tikzcd}\]
~~~
</figure>

1. First, we apply the equivalence `f`. Keeping in mind that `f` is [a
pair](agda://1Lab.Equiv#_≃_) of a function and a proof that this
function is an equivalence, we must project the underlying function to
apply it.

2. Then, we do a vacuous [transport](agda://1Lab.Path#transport) along
the reflexivity path on `B`. While in the case of `ua`{.Agda}, `B`
doesn't depend on `i`, in the general case of `Glue`{.Agda}, it might.
This is where the `transp (λ _ → B) i` in the path term `uaβ`{.Agda}
comes from: We need something that, on the left endpoint, is `transport
refl _`, and on the right endpoint disappears.

3. Finally, we apply the inverse of the identity equivalence, which
computes away, and contributes nothing to the term.

```agda
uaβ : {A B : Type ℓ} (f : A ≃ B) (x : A) → transport (ua f) x ≡ f .fst x
uaβ {A = A} {B} f x i = transp (λ _ → B) i (f .fst x)
```

Since `ua`{.Agda} is a map that turns equivalences into paths, we can
compose it with a function that turns
[isomorphisms](agda://1Lab.Equiv#Iso) into equivalences to get the map
`Iso→path`{.Agda}.

```agda
Iso→path : {A B : Type ℓ} → Iso A B → A ≡ B
Iso→path (f , iiso) = ua (f , isIso→isEquiv iiso)
```

# The “axiom”

```agda
module _ where private
  idToEquiv : {A B : Type ℓ} → A ≡ B → A ≃ B
  idToEquiv {A = A} {B} = J (λ x _ → A ≃ x) (_ , idEquiv)

  idToEquiv-refl : {A : Type ℓ} → idToEquiv (λ i → A) ≡ (_ , idEquiv)
  idToEquiv-refl {A = A} = JRefl (λ x _ → A ≃ x) (_ , idEquiv)
```

The actual “univalence axiom”, as stated in the HoTT book, says that the
canonical map `A ≡ B`, defined using `J`{.Agda}, is an equivalence. This
map is `idToEquiv`{.Agda}, defined right above. In more intuitive terms,
it's "casting" the identity equivalence `A ≃ A` along a proof that `A ≡
B` to get an equivalence `A ≃ B`.

However, because of efficiency concerns (Agda _is_ a programming
language, after all), instead of using `idToEquiv`{.Agda} defined using
J, we use `pathToEquiv`{.Agda}, which is [defined in an auxilliary
module](agda://1Lab.Equiv.FromPath).

```agda
pathToEquiv : {A B : Type ℓ} → A ≡ B → A ≃ B
pathToEquiv p = line→equiv (λ i → p i)

pathToEquiv-refl : {A : Type ℓ} → pathToEquiv (refl {x = A}) ≡ (id , idEquiv)
pathToEquiv-refl {A = A} =
  Σ-Path (λ i x → transp (λ j → A) i x) (isProp-isEquiv _ _ _)
```

```agda
univalence-Iso : {A B : Type ℓ} → Iso (A ≡ B) (A ≃ B)
univalence : {A B : Type ℓ} → isEquiv (pathToEquiv {A = A} {B})
univalence¯¹ : {A B : Type ℓ} → isEquiv (ua {A = A} {B})
```

We can now prove the univalence theorem - this map is an isomorphism,
and thus, an equivalence. First, we need a small lemma that says `ua id
≡ refl`. This will be used to show one direction of the inverse.

```agda
uaIdEquiv : {A : Type ℓ} → ua (_ , idEquiv {A = A}) ≡ refl
uaIdEquiv {A = A} i j = Glue A {φ = i ∨ ~ j ∨ j} (λ _ → A , _ , idEquiv)

univalence-Iso {A = A} {B = B} = pathToEquiv , iiso where
```

This can be shown using `Glue`{.Agda}. There are two interval variables,
this is a path between paths: a square. When `i = i0`, the glue is
stuck[^1], so we get `Glue A (λ _ → A , _ , idEquiv)`. When `i = i1`, by
the argument `φ`, the glue computes away, and we get `refl`, hence the
type.

[^1]: Pardon the pun.

```agda
  iiso : isIso pathToEquiv
  isIso.inv iiso = ua
```

The inverse to `pathToEquiv`{.Agda} is the `ua`{.Agda} map which turns
equivalences into paths.

```agda
  isIso.rinv iiso (f , isEqv) =
    Σ-Path (λ i x → transp (λ i → B) i (f x))
           (isProp-isEquiv f _ _)
```

We have that `pathToEquiv (ua f) ≡ f` in two parts. Since equivalences
are pairs, we can reduce this to proving that the function is preserved,
and proving that the equivalence proof is preserved. The latter follows
from `isEquiv`{.Agda} being a proposition.

For the former, Agda does all the work for us: All we need to show is
that `transport (λ i → B) (f x)` is equal to `f`.  This we do using
`transp`{.Agda}, which, when `i = i1`, behaves like the identity
function.

```agda
  isIso.linv iiso = 
    J (λ _ p → ua (pathToEquiv p) ≡ p)
      (ap ua pathToEquiv-refl ∙ uaIdEquiv)

univalence {A = A} {B} = isIso→isEquiv (univalence-Iso .snd)
univalence¯¹ {A = A} {B} = isIso→isEquiv (isIso.inverse (univalence-Iso .snd))
```

To show that `pathToEquiv (ua p) ≡ p`, we do [path induction] on `p`,
reducing this to showing that `ua (pathToEquiv refl) ≡ refl`. By
`pathToEquiv-refl`{.Agda}, we have that `pathToEquiv refl` is
`idEquiv`{.Agda}, which means the `uaIdEquiv`{.Agda} lemma proves what
we wanted.

[path induction]: agda://1Lab.Path#J

In many situations, it is helpful to have a proof that
`pathToEquiv`{.Agda} followed by `an adjustment of levels`{.Agda
ident=Lift} is still an equivalence:

```agda
univalence-lift : {A B : Type ℓ} → isEquiv (λ e → lift (pathToEquiv {A = A} {B} e))
univalence-lift {ℓ = ℓ} = isIso→isEquiv morp where
  morp : isIso (λ e → lift {ℓ = lsuc ℓ} (pathToEquiv e))
  morp .isIso.inv x = ua (x .Lift.lower)
  morp .isIso.rinv x =
    lift (pathToEquiv (ua (x .Lift.lower))) ≡⟨ ap lift (univalence-Iso .snd .isIso.rinv _) ⟩
    x                                       ∎
  morp .isIso.linv x = univalence-Iso .snd .isIso.linv _
```


## Consequences

One useful consequence of the fact that `(A ≡ B) ≡ (A ≃ B)`[^2] is that
the type of _equivalences_ satisfies [the same induction principle] as
the type of _equalities_. What I mean, precisely, is that the type `Σ B
(A ≃ B)` is contractible, like the type `Σ B (A ≡ B)`. From this, we get
"equivalence induction": `EquivJ`{.Agda}.

[the same induction principle]: agda://1Lab.Path#J

```agda
EquivContr : ∀ {ℓ} (A : Type ℓ) → isContr (Σ[ B ∈ Type ℓ ] A ≃ B)
isContr.centre (EquivContr A)          = A , _ , idEquiv
isContr.paths (EquivContr A) (B , A≃B) = Σ-Path (ua A≃B) (Σ-Path p q)
  where
    p : _
    p i x = transp (λ i → B) i (fst A≃B (transp (λ j → A) i x))

    q : _
    q = isProp-isEquiv (A≃B .fst) _ _
```

We can use the same decomposition of `J`{.Agda} as transport +
contractibility of singletons for equivalences. Since we have that `(A ,
_ , idEquiv) ≡ (B , eqv)`, we can transport a proof of `P (A , _)` to a
proof of `P (B , eqv)`. Modulo currying, this is exactly the same thing
as `J`{.Agda}.

```agda
EquivJ : ∀ {ℓ ℓ'} {A : Type ℓ}
       → (P : (B : Type ℓ) → A ≃ B → Type ℓ')
       → P A (_ , idEquiv)
       → {B : Type ℓ} (e : A ≃ B)
       → P B e
EquivJ P pid eqv =
  subst (λ e → P (e .fst) (e .snd))
        (EquivContr _ .isContr.paths (_ , eqv))
        pid
```

[^2]: Not the fundamental theorem of engineering!

Equivalence induction makes proving several properties about
equivalences almost trivial. For example, if `f` is an equivalence, then
so is its action on paths. 

```agda
isEquiv→isEmbedding : ∀ {ℓ} {A B : Type ℓ}
                    → (f : A → B) → isEquiv f
                    → {x y : A}
                    → isEquiv (ap f {x = x} {y = y})
isEquiv→isEmbedding f eqv =
  EquivJ
    (λ B e → isEquiv (ap (e .fst)))
    idEquiv
    (f , eqv)
```

The proof can be rendered in English roughly as follows:

> Suppose $f : A \to B$ `is an equivalence`{.Agda ident=isEquiv}. We want to
show that, for any choice of $x, y : A$, the map $\mathrm{ap}(f)_{x,y} :
x \equiv y \to f(x) \equiv f(y)$ is an equivalence.
>
> By `induction`{.Agda ident=EquivJ}, it suffices to cover the case
where $B$ is $A$, and $f$ is the identity function.
>
> But then, we have that $\mathrm{ap}(\mathrm{id})$ is [definitionally
equal](agda://1Lab.Path#ap-id) to $\mathrm{id}$, which is known to be
`an equivalence`{.Agda ident=idEquiv}. <span class=qed>$\blacksquare$</span>

## Paths over `ua`

A very useful theorem is a specialisation of `PathP≡Path`{.Agda} to the
case of paths dependent over `ua`{.Agda}. This is proven using the
following cubical helpers, which use the glueing primitives:

```agda
ua-unglue : ∀ {A B : Type ℓ} (e : A ≃ B) (i : I) (x : ua e i)
            → B [ _ ↦ (λ { (i = i0) → e .fst x ; (i = i1) → x }) ]
ua-unglue e i x = inS (unglue (i ∨ ~ i) x)

ua-glue : ∀ {A B : Type ℓ} (e : A ≃ B) (i : I) (x : Partial (~ i) A)
            (y : B [ _ ↦ (λ { (i = i0) → e .fst (x 1=1) }) ])
          → ua e i [ _ ↦ (λ { (i = i0) → x 1=1 ; (i = i1) → outS y }) ]
ua-glue e i x y = inS (prim^glue {φ = i ∨ ~ i}
                                 (λ { (i = i0) → x 1=1
                                    ; (i = i1) → outS y })
                                 (outS y))
```

Fortunately, the types of these shrink a lot if the interval variable is
factored in:

```agda
uaPathP→Path : ∀ {A B : Type ℓ} (e : A ≃ B) {x : A} {y : B}
             → PathP (λ i → ua e i) x y
             → e .fst x ≡ y
uaPathP→Path e p i = outS (ua-unglue e i (p i))

Path→uaPathP : ∀ {A B : Type ℓ} (e : A ≃ B) {x : A} {y : B}
             → e .fst x ≡ y
             → PathP (λ i → ua e i) x y
Path→uaPathP e {x = x} p i = outS (ua-glue e i (λ { (i = i0) → x }) (inS (p i)))
```

These functions are definitional inverses, and thus they provide a
characterisation of `PathP (ua f)` in terms of non-dependent paths:

```agda
uaPathP≃Path : ∀ {A B : Type ℓ} (e : A ≃ B) {x : A} {y : B}
             → (e .fst x ≡ y) ≃ (PathP (λ i → ua e i) x y)
uaPathP≃Path eqv .fst = Path→uaPathP eqv
uaPathP≃Path eqv .snd .isEqv y .centre = strict-fibres (uaPathP→Path eqv) y .fst
uaPathP≃Path eqv .snd .isEqv y .paths = strict-fibres (uaPathP→Path eqv) y .snd
```
