```agda
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.HLevel where
```

# h-Levels

The "homotopy level" (h-level for short) of a type is a measure of how
[truncated] it is, where the numbering is offset by 2. Specifically, a
(-2)-truncated type is a type of h-level 0. In another sense, h-level
measures how "homotopically interesting" a given type is:

* The contractible types are maximally uninteresting because there is
only one.

* The only interesting information about a proposition is whether it is
inhabited.

* The interesting information about a set is the collection of its inhabitants.

* The interesting information about a groupoid includes, in addition to
its inhabitants, the way those are related by paths. As an extreme
example, the delooping groupoid of a group -- for instance, [the circle] --
has uninteresting points (there's only one), but interesting _loops_.

[the circle]: agda://Homotopy.Space.Circle

For convenience, we refer to the collection of types of h-level $n$ as
_homotopy $(n-2)$-types_. For instance: "The sets are the homotopy
0-types". The use of the $-2$ offset is so the naming here matches that
of the HoTT book.

The h-levels are defined by induction, where the base case are the
_contractible types_.

[truncated]: https://ncatlab.org/nlab/show/truncated+object

```agda
record is-contr {ℓ} (A : Type ℓ) : Type ℓ where
  constructor contr
  field
    centre : A
    paths : (x : A) → centre ≡ x

open is-contr public
```

A contractible type is one for which the unique map `X → ⊤` is an
equivalence. Thus, it has "one element". This doesn't mean that we can't
have "multiple", distinctly named, inhabitants of the type; It means any
inhabitants of the type must be connected by a path, and this path must
be picked uniformly.

```agda
module _ where
  data [0,1] : Type where
    ii0 : [0,1]
    ii1 : [0,1]
    seg : ii0 ≡ ii1
```

An example of a contractible type that is not _directly_ defined as
another name for `⊤` is the unit interval, defined as a higher inductive
type.

```agda
  interval-contractible : is-contr [0,1]
  interval-contractible .centre = ii0
  interval-contractible .paths ii0 i = ii0
  interval-contractible .paths ii1 i = seg i
  interval-contractible .paths (seg i) j = seg (i ∧ j)
```

A type is (n+1)-truncated if its path types are all n-truncated.
However, if we directly take this as the definition, the types we end up
with are very inconvenient! That's why we introduce this immediate step:
An **h-proposition**, or **proposition** for short, is a type where any
two elements are connected by a path.

```agda
is-prop : ∀ {ℓ} → Type ℓ → Type _
is-prop A = (x y : A) → x ≡ y
```

With this, we can define the `is-hlevel`{.Agda} predicate. For h-levels
greater than zero, this definition results in much simpler types!

```agda
is-hlevel : ∀ {ℓ} → Type ℓ → Nat → Type _
is-hlevel A 0 = is-contr A
is-hlevel A 1 = is-prop A
is-hlevel A (suc n) = (x y : A) → is-hlevel (Path A x y) n
```

Since types of h-level 2 are very common, they get a special name:
**h-sets**, or just **sets** for short. This is justified because we can
think of classical sets as being equipped with an equality _proposition_
$x = y$ - having propositional paths is exactly the definition of
`is-set`{.Agda}.  The universe of all types that are sets, is,
correspondingly, called **Set**.

```agda
is-set : ∀ {ℓ} → Type ℓ → Type ℓ
is-set A = is-hlevel A 2
```

Similarly, the types of h-level 3 are called **groupoids**.

```agda
is-groupoid : ∀ {ℓ} → Type ℓ → Type ℓ
is-groupoid A = is-hlevel A 3
```

---

```agda
private
  variable
    ℓ : Level
    A : Type ℓ
```

# Preservation of h-levels

If a type is of h-level $n$, then it's automatically of h-level $k+n$,
for any $k$. We first prove a couple of common cases that deserve their
own names:

```agda
is-contr→is-prop : is-contr A → is-prop A
is-contr→is-prop C x y i = hcomp (∂ i) λ where
  j (i = i0) → C .paths x j
  j (i = i1) → C .paths y j
  j (j = i0) → C .centre
```

<!--
```agda
is-contr→extend : is-contr A → (φ : I) (p : Partial φ A) → A [ φ ↦ p ]
is-contr→extend C φ p = inS (hcomp φ
  λ { j (φ = i1) → C .paths (p 1=1) j
    ; j (j = i0) → C .centre
    })

extend→is-contr : (∀ φ (p : Partial φ A) → A [ φ ↦ p ]) → is-contr A
extend→is-contr ext = contr (outS (ext i0 λ ())) λ x i → outS (ext i λ _ → x)

is-contr→is-set : is-contr A → is-set A
is-contr→is-set C x y p q i j = outS (is-contr→extend C (∂ i ∨ ∂ j) λ where
  (i = i0) → p j
  (i = i1) → q j
  (j = i0) → x
  (j = i1) → y)

SingletonP : ∀ {ℓ} (A : I → Type ℓ) (a : A i0) → Type _
SingletonP A a = Σ[ x ∈ A i1 ] PathP A a x

SinglP-is-contr : ∀ {ℓ} (A : I → Type ℓ) (a : A i0) → is-contr (SingletonP A a)
SinglP-is-contr A a .centre = _ , transport-filler (λ i → A i) a
SinglP-is-contr A a .paths (x , p) i = _ , λ j → fill A (∂ i) j λ where
  j (i = i0) → coe0→i A j a
  j (i = i1) → p j
  j (j = i0) → a

SinglP-is-prop : ∀ {ℓ} {A : I → Type ℓ} {a : A i0} → is-prop (SingletonP A a)
SinglP-is-prop = is-contr→is-prop (SinglP-is-contr _ _)
```
-->

This enables another useful characterisation of being a proposition,
which is that the propositions are precisely the types which are
contractible when they are inhabited:

```agda
contractible-if-inhabited : ∀ {ℓ} {A : Type ℓ} → (A → is-contr A) → is-prop A
contractible-if-inhabited cont x y = is-contr→is-prop (cont x) x y
```

The proof that any contractible type is a proposition is not too
complicated. We can get a line connecting any two elements as the lid of
the square below:

~~~{.quiver}
\[\begin{tikzcd}
  x && y \\
  \\
  {C \id{.centre}} && {C .\id{centre}}
  \arrow[dashed, from=1-1, to=1-3]
  \arrow["{C \id{.paths}\ x\ j}", from=3-1, to=1-1]
  \arrow["{C \id{.paths}\ y\ j}"', from=3-3, to=1-3]
  \arrow["{C \id{.centre}}"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

This is equivalently the composition of `sym (C .paths x) ∙ C.paths y` -
a path $x \to y$ which factors through the `centre`{.Agda}. The direct
cubical description is, however, slightly more efficient.

```agda
is-prop→is-set : is-prop A → is-set A
is-prop→is-set h x y p q i j = hcomp (∂ i ∨ ∂ j) λ where
  k (i = i0) → h x (p j) k
  k (i = i1) → h x (q j) k
  k (j = i0) → h x x k
  k (j = i1) → h x y k
  k (k = i0) → x
```

The proof that any proposition is a set is slightly more complicated.
Since the desired homotopy `p ≡ q` is a square, we need to describe a
_cube_ where the missing face is the square we need. I have
painstakingly illustrated it here:

~~~{.quiver .tall-2}
\[\begin{tikzcd}
  \textcolor{rgb,255:red,214;green,92;blue,92}{x} &&&& \textcolor{rgb,255:red,214;green,92;blue,92}{y} \\
  & \textcolor{rgb,255:red,92;green,92;blue,214}{x} && \textcolor{rgb,255:red,92;green,92;blue,214}{x} \\
  \\
  & \textcolor{rgb,255:red,92;green,92;blue,214}{x} && \textcolor{rgb,255:red,92;green,92;blue,214}{x} \\
  \textcolor{rgb,255:red,214;green,92;blue,92}{x} &&&& \textcolor{rgb,255:red,214;green,92;blue,92}{y}
  \arrow[""{name=0, anchor=center, inner sep=0}, "p", color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=1-5]
  \arrow[""{name=1, anchor=center, inner sep=0}, "q"', color={rgb,255:red,214;green,92;blue,92}, from=5-1, to=5-5]
  \arrow[""{name=2, anchor=center, inner sep=0}, color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=5-1]
  \arrow[""{name=3, anchor=center, inner sep=0}, color={rgb,255:red,214;green,92;blue,92}, from=1-5, to=5-5]
  \arrow[""{name=4, anchor=center, inner sep=0}, color={rgb,255:red,92;green,92;blue,214}, from=2-2, to=2-4]
  \arrow[""{name=5, anchor=center, inner sep=0}, color={rgb,255:red,92;green,92;blue,214}, from=2-2, to=4-2]
  \arrow[""{name=6, anchor=center, inner sep=0}, color={rgb,255:red,92;green,92;blue,214}, from=2-4, to=4-4]
  \arrow[""{name=7, anchor=center, inner sep=0}, color={rgb,255:red,92;green,92;blue,214}, from=4-2, to=4-4]
  \arrow[from=4-4, to=5-5]
  \arrow[from=2-4, to=1-5]
  \arrow[from=2-2, to=1-1]
  \arrow[from=4-2, to=5-1]
  \arrow["x"{description}, color={rgb,255:red,92;green,92;blue,214}, Rightarrow, draw=none, from=4, to=7]
  \arrow["{h\ x\ p(j)\ k}"{description}, Rightarrow, draw=none, from=4, to=0]
  \arrow["{h\ x\ q(j)\ k}"{description}, Rightarrow, draw=none, from=7, to=1]
  \arrow["{h\ x\ x\ k}"{description}, Rightarrow, draw=none, from=5, to=2]
  \arrow["{h\ y\ y\ k}"', Rightarrow, draw=none, from=6, to=3]
\end{tikzcd}\]
~~~

To set your perspective: You are looking at a cube that has a
transparent front face. The front face has four `x` corners, and four `λ
i → x` edges. Each double arrow pointing from the front face to the back
face is one of the sides of the composition. They're labelled with the
terms in the `hcomp`{.Agda} for `is-prop→is-set`{.Agda}: For example, the
square you get when fixing `i = i0` is on top of the diagram. Since we
have an open box, it has a lid --- which, in this case, is the back face
--- which expresses the identification we wanted: `p ≡ q`.

With these two base cases, we can prove the general case by recursion:

```agda
is-hlevel-suc : ∀ {ℓ} {A : Type ℓ} (n : Nat) → is-hlevel A n → is-hlevel A (suc n)
is-hlevel-suc 0 x = is-contr→is-prop x
is-hlevel-suc 1 x = is-prop→is-set x
is-hlevel-suc (suc (suc n)) h x y = is-hlevel-suc (suc n) (h x y)
```

By another inductive argument, we can prove that any offset works:

```agda
is-hlevel-+ : ∀ {ℓ} {A : Type ℓ} (n k : Nat) → is-hlevel A n → is-hlevel A (k + n)
is-hlevel-+ n zero x    = x
is-hlevel-+ n (suc k) x = is-hlevel-suc _ (is-hlevel-+ n k x)
```

A very convenient specialisation of the argument above is that if $A$ is
a proposition, then it has any non-zero h-level:

```agda
is-prop→is-hlevel-suc
  : ∀ {ℓ} {A : Type ℓ} {n : Nat} → is-prop A → is-hlevel A (suc n)
is-prop→is-hlevel-suc {n = zero} aprop = aprop
is-prop→is-hlevel-suc {n = suc n} aprop =
  is-hlevel-suc (suc n) (is-prop→is-hlevel-suc aprop)
```

Furthermore, by the upwards closure of h-levels, we have that if $A$ is
an n-type, then paths in $A$ are also $n$-types. This is because, by
definition, the paths in a $n$-type are "$(n-1)$-types", which
`is-hlevel-suc`{.Agda} extends into $n$-types.

```agda
Path-is-hlevel : ∀ {ℓ} {A : Type ℓ} (n : Nat) → is-hlevel A n → {x y : A}
               → is-hlevel (x ≡ y) n
Path-is-hlevel zero ahl =
  contr (is-contr→is-prop ahl _ _)
        λ x → is-prop→is-set (is-contr→is-prop ahl) _ _ _ x
Path-is-hlevel (suc n) ahl = is-hlevel-suc (suc n) ahl _ _

PathP-is-hlevel : ∀ {ℓ} {A : I → Type ℓ} (n : Nat)
                 → is-hlevel (A i1) n
                 → {x : A i0} {y : A i1}
                 → is-hlevel (PathP A x y) n
PathP-is-hlevel {A = A} n ahl {x} {y} =
  subst (λ e → is-hlevel e n) (sym (PathP≡Path A x y)) (Path-is-hlevel n ahl)
```

<!--
```
Path-is-hlevel' : (n : Nat) → is-hlevel A (suc n) → (x y : A) → is-hlevel (x ≡ y) n
Path-is-hlevel' 0 ahl x y =
  contr (ahl x y) λ x → is-prop→is-set ahl _ _ _ x

Path-is-hlevel' (suc n) h x y = h x y

PathP-is-hlevel' : ∀ {ℓ} {A : I → Type ℓ} (n : Nat)
                  → is-hlevel (A i1) (suc n)
                  → (x : A i0) (y : A i1)
                  → is-hlevel (PathP A x y) n
PathP-is-hlevel' {A = A} n ahl x y =
  subst (λ e → is-hlevel e n) (sym (PathP≡Path A x y)) (Path-is-hlevel' n ahl _ _)
```
-->

# is-hlevel is a proposition

Perhaps surprisingly, "being of h-level n" is a proposition, for any n!
To get an intuitive feel for why this might be true before we go prove
it, I'd like to suggest an alternative interpretation of the proposition
`is-hlevel A n`: The type `A` admits _unique_ fillers for any `n`-cube.

A contractible type is one that has a unique point: It has a unique
filler for the 0-cube, which is a point. A proposition is a type
that admits unique fillers for 1-cubes, which are lines: given any
endpoint, there is a line that connects them. A set is a type that
admits unique fillers for 2-cubes, or squares, and so on.

Since these fillers are _unique_, if a type has them, it has them in at
most one way!

```agda
is-contr-is-prop : is-prop (is-contr A)
is-contr-is-prop {A = A} (contr c₁ h₁) (contr c₂ h₂) i .centre = h₁ c₂ i
is-contr-is-prop {A = A} (contr c₁ h₁) (contr c₂ h₂) i .paths x j =
  hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → h₁ (h₁ x j) k
    k (i = i1) → h₁ (h₂ x j) k
    k (j = i0) → h₁ (h₁ c₂ i) k
    k (j = i1) → h₁ x k
    k (k = i0) → c₁
```

First, we prove that being contractible is a proposition. Next, we prove
that being a proposition is a proposition. This follows from
`is-prop→is-set`{.Agda}, since what we want to prove is that `h₁` and `h₂`
always give homotopic paths.

```agda
is-prop-is-prop : is-prop (is-prop A)
is-prop-is-prop {A = A} h₁ h₂ i x y = is-prop→is-set h₁ x y (h₁ x y) (h₂ x y) i
```

Now we can prove the general case by the same inductive argument we used
to prove h-levels can be raised:

```agda
is-hlevel-is-prop : ∀ {ℓ} {A : Type ℓ} (n : Nat) → is-prop (is-hlevel A n)
is-hlevel-is-prop 0 = is-contr-is-prop
is-hlevel-is-prop 1 = is-prop-is-prop
is-hlevel-is-prop (suc (suc n)) x y i a b =
  is-hlevel-is-prop (suc n) (x a b) (y a b) i
```

# Dependent h-Levels

In cubical type theory, it's natural to consider a notion of _dependent_
h-level for a _family_ of types, where, rather than having (e.g.)
`Path`{.Agda}s for any two elements, we have `PathP`{.Agda}s. Since
dependent contractibility doesn't make a lot of sense, this definition
is offset by one to start at the propositions.

```agda
is-hlevel-dep : ∀ {ℓ ℓ'} {A : Type ℓ} → (A → Type ℓ') → Nat → Type _

is-hlevel-dep B zero =
  ∀ {x y} (α : B x) (β : B y) (p : x ≡ y)
  → PathP (λ i → B (p i)) α β

is-hlevel-dep B (suc n) =
  ∀ {a0 a1} (b0 : B a0) (b1 : B a1)
  → is-hlevel-dep {A = a0 ≡ a1} (λ p → PathP (λ i → B (p i)) b0 b1) n
```

It's sufficient for a type family to be of an h-level everywhere for the
whole family to be the same h-level.

```agda
is-prop→pathp : ∀ {B : I → Type ℓ} → ((i : I) → is-prop (B i))
              → (b0 : B i0) (b1 : B i1)
              → PathP (λ i → B i) b0 b1
is-prop→pathp {B = B} hB b0 b1 = to-pathp (hB _ _ _)
```

The base case is turning a proof that a type is a proposition uniformly
over the interval to a filler for any PathP.

```agda
is-hlevel→is-hlevel-dep
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
  → (n : Nat) → ((x : A) → is-hlevel (B x) (suc n))
  → is-hlevel-dep B n
is-hlevel→is-hlevel-dep zero hl α β p = is-prop→pathp (λ i → hl (p i)) α β
is-hlevel→is-hlevel-dep {A = A} {B = B} (suc n) hl {a0} {a1} b0 b1 =
  is-hlevel→is-hlevel-dep n (λ p → helper a1 p b1)
  where
    helper : (a1 : A) (p : a0 ≡ a1) (b1 : B a1)
           → is-hlevel (PathP (λ i → B (p i)) b0 b1) (suc n)
    helper a1 p b1 =
      J (λ a1 p → ∀ b1 → is-hlevel (PathP (λ i → B (p i)) b0 b1) (suc n))
        (λ _ → hl _ _ _) p b1
```

<!--
```agda
is-prop→squarep
  : ∀ {B : I → I → Type ℓ} → ((i j : I) → is-prop (B i j))
  → {a : B i0 i0} {b : B i0 i1} {c : B i1 i0} {d : B i1 i1}
  → (p : PathP (λ j → B j i0) a c)
  → (q : PathP (λ j → B i0 j) a b)
  → (s : PathP (λ j → B i1 j) c d)
  → (r : PathP (λ j → B j i1) b d)
  → SquareP B p q s r
is-prop→squarep {B = B} is-propB {a = a} p q s r i j =
  hcomp (∂ j ∨ ∂ i) λ where
    k (j = i0) → is-propB i j (base i j) (p i) k
    k (j = i1) → is-propB i j (base i j) (r i) k
    k (i = i0) → is-propB i j (base i j) (q j) k
    k (i = i1) → is-propB i j (base i j) (s j) k
    k (k = i0) → base i j
  where
    base : (i j : I) → B i j
    base i j = transport (λ k → B (i ∧ k) (j ∧ k)) a

is-prop→pathp-is-contr
  : {A : I → Type ℓ} → ((i : I) → is-prop (A i))
  → (x : A i0) (y : A i1) → is-contr (PathP A x y)
is-prop→pathp-is-contr ap x y .centre = is-prop→pathp ap x y
is-prop→pathp-is-contr ap x y .paths p =
  is-prop→squarep (λ i j → ap j) refl _ _ refl

abstract
  is-set→squarep :
    {A : I → I → Type ℓ}
    (is-set : (i j : I) → is-set (A i j))
    → {a : A i0 i0} {b : A i0 i1} {c : A i1 i0} {d : A i1 i1}
    → (p : PathP (λ j → A j i0) a c)
    → (q : PathP (λ j → A i0 j) a b)
    → (s : PathP (λ j → A i1 j) c d)
    → (r : PathP (λ j → A j i1) b d)
    → SquareP A p q s r
  is-set→squarep isset a₀₋ a₁₋ a₋₀ a₋₁ =
    transport (sym (PathP≡Path _ _ _))
              (PathP-is-hlevel' 1 (isset _ _) _ _ _ _)

-- Has to go through:
_ : ∀ {A : Type} {a b c d : A} (p : a ≡ c) (q : a ≡ b) (s : c ≡ d) (r : b ≡ d)
  → Square p q s r ≡ SquareP (λ _ _ → A) p q s r
_ = λ _ _ _ _ → refl
```
-->
