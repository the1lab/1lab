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

[the circle]: agda://1Lab.HIT.S1

For convenience, we refer to the collection of types of h-level $n$ as
_homotopy $(n-2)$-types_. For instance: "The sets are the homotopy
0-types". The use of the $-2$ offset is so the naming here matches that
of the HoTT book.

The h-levels are defined by induction, where the base case are the
_contractible types_.

[truncated]: https://ncatlab.org/nlab/show/truncated+object

```agda
record isContr {ℓ} (A : Type ℓ) : Type ℓ where
  constructor contr
  field
    centre : A
    paths : (x : A) → centre ≡ x

open isContr public
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
  interval-contractible : isContr [0,1]
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
isProp : ∀ {ℓ} → Type ℓ → Type _
isProp A = (x y : A) → x ≡ y
```

With this, we can define the `isHLevel`{.Agda} predicate. For h-levels
greater than zero, this definition results in much simpler types!

```agda
isHLevel : ∀ {ℓ} → Type ℓ → Nat → Type _
isHLevel A 0 = isContr A
isHLevel A 1 = isProp A
isHLevel A (suc n) = (x y : A) → isHLevel (Path A x y) n
```

Since types of h-level 2 are very common, they get a special name:
**h-sets**, or just **sets** for short. This is justified because we can
think of classical sets as being equipped with an equality _proposition_
$x = y$ - having propositional paths is exactly the definition of
`isSet`{.Agda}.  The universe of all types that are sets, is,
correspondingly, called **Set**.

```agda
isSet : ∀ {ℓ} → Type ℓ → Type ℓ
isSet A = isHLevel A 2

Set : (ℓ : Level) → Type (lsuc ℓ)
Set ℓ = Σ (isSet {ℓ = ℓ})
```

<!--
```agda
Prop : (ℓ : Level) → Type (lsuc ℓ)
Prop ℓ = Σ (isProp {ℓ = ℓ})
```
-->

Similarly, the types of h-level 3 are called **groupoids**.

```agda
isGroupoid : ∀ {ℓ} → Type ℓ → Type ℓ
isGroupoid A = isHLevel A 3
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
isContr→isProp : isContr A → isProp A
isContr→isProp C x y i =
  hcomp (λ j → λ { (i = i0) → C .paths x j
                 ; (i = i1) → C .paths y j
                 } )
        (C .centre)
```

<!--
```agda
SingletonP : ∀ {ℓ} (A : I → Type ℓ) (a : A i0) → Type _
SingletonP A a = Σ[ x ∈ A i1 ] PathP A a x

isContrSinglP : ∀ {ℓ} (A : I → Type ℓ) (a : A i0) → isContr (SingletonP A a)
isContrSinglP A a .centre = _ , transport-filler (λ i → A i) a
isContrSinglP A a .paths (x , p) i =
  _ , λ j → fill A (λ j → λ {(i = i0) → transport-filler (λ i → A i) a j; (i = i1) → p j}) (inS a) j

isPropSinglP : ∀ {ℓ} {A : I → Type ℓ} {a : A i0} → isProp (SingletonP A a)
isPropSinglP = isContr→isProp (isContrSinglP _ _)
```
-->

This enables another useful characterisation of being a proposition,
which is that the propositions are precisely the types which are
contractible when they are inhabited:

```agda
inhContr→isProp : ∀ {ℓ} {A : Type ℓ} → (A → isContr A) → isProp A
inhContr→isProp cont x y = isContr→isProp (cont x) x y
```

The proof that any contractible type is a proposition is not too
complicated. We can get a line connecting any two elements as the lid of
the square below:

~~~{.quiver}
\[\begin{tikzcd}
  x && y \\
  \\
  {C \mathrm{.centre}} && {C .\mathrm{centre}}
  \arrow[dashed, from=1-1, to=1-3]
  \arrow["{C \mathrm{.paths}\ x\ j}", from=3-1, to=1-1]
  \arrow["{C \mathrm{.paths}\ y\ j}"', from=3-3, to=1-3]
  \arrow["{C \mathrm{.centre}}"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

This is equivalently the composition of `sym (C .paths x) ∙ C.paths y` -
a path $x \to y$ which factors through the `centre`{.Agda}. The direct
cubical description is, however, slightly more efficient.

```agda
isProp→isSet : isProp A → isSet A
isProp→isSet h x y p q i j =
  hcomp (λ k → λ { (i = i0) → h x (p j) k
                 ; (i = i1) → h x (q j) k
                 ; (j = i0) → h x x k
                 ; (j = i1) → h x y k
                 })
        x
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
terms in the `hcomp`{.Agda} for `isProp→isSet`{.Agda}: For example, the
square you get when fixing `i = i0` is on top of the diagram. Since we
have an open box, it has a lid --- which, in this case, is the back face
--- which expresses the identification we wanted: `p ≡ q`.

With these two base cases, we can prove the general case by recursion:

```agda
isHLevel-suc : ∀ {ℓ} {A : Type ℓ} (n : Nat) → isHLevel A n → isHLevel A (suc n)
isHLevel-suc 0 x = isContr→isProp x
isHLevel-suc 1 x = isProp→isSet x
isHLevel-suc (suc (suc n)) h x y = isHLevel-suc (suc n) (h x y)
```

By another inductive argument, we can prove that any offset works:

```agda
isHLevel-+ : ∀ {ℓ} {A : Type ℓ} (n k : Nat) → isHLevel A n → isHLevel A (k + n)
isHLevel-+ n zero x    = x
isHLevel-+ n (suc k) x = isHLevel-suc _ (isHLevel-+ n k x)
```

A very convenient specialisation of the argument above is that if $A$ is
a proposition, then it has any non-zero h-level:

```agda
isProp→isHLevel-suc : ∀ {ℓ} {A : Type ℓ} {n : Nat} → isProp A → isHLevel A (suc n)
isProp→isHLevel-suc {n = zero} aprop = aprop
isProp→isHLevel-suc {n = suc n} aprop =
  isHLevel-suc (suc n) (isProp→isHLevel-suc aprop)
```

Furthermore, by the upwards closure of h-levels, we have that if $A$ is
an n-type, then paths in $A$ are also $n$-types. This is because, by
definition, the paths in a $n$-type are "$(n-1)$-types", which
`isHLevel-suc`{.Agda} extends into $n$-types.

```agda
isHLevelPath : ∀ {ℓ} {A : Type ℓ} (n : Nat) → isHLevel A n → {x y : A}
             → isHLevel (x ≡ y) n
isHLevelPath zero ahl =
  contr (isContr→isProp ahl _ _)
        λ x → isProp→isSet (isContr→isProp ahl) _ _ _ x
isHLevelPath (suc n) ahl = isHLevel-suc (suc n) ahl _ _

isHLevelPathP : ∀ {ℓ} {A : I → Type ℓ} (n : Nat)
              → isHLevel (A i1) n
              → {x : A i0} {y : A i1}
              → isHLevel (PathP A x y) n
isHLevelPathP {A = A} n ahl {x} {y} =
  subst (λ e → isHLevel e n)
        (sym (PathP≡Path A x y))
        (isHLevelPath n ahl)
```

<!--
```
isHLevelPath' : (n : Nat) → isHLevel A (suc n) → (x y : A) → isHLevel (x ≡ y) n
isHLevelPath' 0 ahl x y =
  contr (ahl x y)
        λ x → isProp→isSet ahl _ _ _ x
isHLevelPath' (suc n) h x y = h x y

isHLevelPathP' : ∀ {ℓ} {A : I → Type ℓ} (n : Nat)
               → isHLevel (A i1) (suc n)
               → (x : A i0) (y : A i1)
               → isHLevel (PathP A x y) n
isHLevelPathP' {A = A} n ahl x y =
  subst (λ e → isHLevel e n)
        (sym (PathP≡Path A x y))
        (isHLevelPath' n ahl _ _)
```
-->

# isHLevel is a proposition

Perhaps surprisingly, "being of h-level n" is a proposition, for any n!
To get an intuitive feel for why this might be true before we go prove
it, I'd like to suggest an alternative interpretation of the proposition
`isHLevel A n`: The type `A` admits _unique_ fillers for any `n`-cube.

A contractible type is one that has a unique point: It has a unique
filler for the 0-cube, which is a point. A proposition is a type
that admits unique fillers for 1-cubes, which are lines: given any
endpoint, there is a line that connects them. A set is a type that
admits unique fillers for 2-cubes, or squares, and so on.

Since these fillers are _unique_, if a type has them, it has them in at
most one way!

```agda
isProp-isContr : isProp (isContr A)
isProp-isContr {A = A} (contr c₁ h₁) (contr c₂ h₂) i =
  record { centre = h₁ c₂ i
         ; paths = λ x j → hcomp (λ k → λ { (i = i0) → h₁ (h₁ x j) k 
                                          ; (i = i1) → h₁ (h₂ x j) k
                                          ; (j = i0) → h₁ (h₁ c₂ i) k
                                          ; (j = i1) → h₁ x k })
                                 c₁
         }
```

First, we prove that being contractible is a proposition. Next, we prove
that being a proposition is a proposition. This follows from
`isProp→isSet`{.Agda}, since what we want to prove is that `h₁` and `h₂`
always give homotopic paths.

```agda
isProp-isProp : isProp (isProp A)
isProp-isProp {A = A} h₁ h₂ i x y = isProp→isSet h₁ x y (h₁ x y) (h₂ x y) i
```

Now we can prove the general case by the same inductive argument we used
to prove h-levels can be raised:

```agda
isProp-isHLevel : ∀ {ℓ} {A : Type ℓ} (n : Nat) → isProp (isHLevel A n)
isProp-isHLevel 0 = isProp-isContr
isProp-isHLevel 1 = isProp-isProp
isProp-isHLevel (suc (suc n)) x y i a b = isProp-isHLevel (suc n) (x a b) (y a b) i
```

# Dependent h-Levels

In cubical type theory, it's natural to consider a notion of _dependent_
h-level for a _family_ of types, where, rather than having (e.g.)
`Path`{.Agda}s for any two elements, we have `PathP`{.Agda}s. Since
dependent contractibility doesn't make a lot of sense, this definition
is offset by one to start at the propositions.

```agda
isHLevelDep : ∀ {ℓ ℓ'} {A : Type ℓ} → (A → Type ℓ') → Nat → Type _
isHLevelDep B zero = ∀ {x y} (α : B x) (β : B y) (p : x ≡ y)
                   → PathP (λ i → B (p i)) α β
isHLevelDep B (suc n) =
   ∀ {a0 a1} (b0 : B a0) (b1 : B a1)
   → isHLevelDep {A = a0 ≡ a1} (λ p → PathP (λ i → B (p i)) b0 b1) n
```

It's sufficient for a type family to be of an h-level everywhere for the
whole family to be the same h-level.

```agda
isProp→PathP : ∀ {B : I → Type ℓ} → ((i : I) → isProp (B i))
             → (b0 : B i0) (b1 : B i1)
             → PathP (λ i → B i) b0 b1
isProp→PathP {B = B} hB b0 b1 = toPathP _ _ _ (hB _ _ _)
```

The base case is turning a proof that a type is a proposition uniformly
over the interval to a filler for any PathP.

```agda
isHLevel→isHLevelDep : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
                     → (n : Nat) → ((x : A) → isHLevel (B x) (suc n))
                     → isHLevelDep B n
isHLevel→isHLevelDep zero hl α β p = isProp→PathP (λ i → hl (p i)) α β
isHLevel→isHLevelDep {A = A} {B = B} (suc n) hl {a0} {a1} b0 b1 =
  isHLevel→isHLevelDep n (λ p → helper a1 p b1)
  where
    helper : (a1 : A) (p : a0 ≡ a1) (b1 : B a1)
           → isHLevel (PathP (λ i → B (p i)) b0 b1) (suc n)
    helper a1 p b1 = J (λ a1 p → ∀ b1 → isHLevel (PathP (λ i → B (p i)) b0 b1) (suc n))
                      (λ _ → hl _ _ _) p b1
```

<!--
```agda
isProp→SquareP : ∀ {B : I → I → Type ℓ} → ((i j : I) → isProp (B i j))
             → {a : B i0 i0} {b : B i0 i1} {c : B i1 i0} {d : B i1 i1}
             → (p : PathP (λ j → B j i0) a c)
             → (q : PathP (λ j → B i0 j) a b)
             → (s : PathP (λ j → B i1 j) c d)
             → (r : PathP (λ j → B j i1) b d)
             → SquareP B p q s r
isProp→SquareP {B = B} isPropB {a = a} p q s r i j =
  hcomp (λ { k (j = i0) → isPropB i j (base i j) (p i) k
           ; k (j = i1) → isPropB i j (base i j) (r i) k
           ; k (i = i0) → isPropB i j (base i j) (q j) k
           ; k (i = i1) → isPropB i j (base i j) (s j) k
        }) (base i j) where
    base : (i j : I) → B i j
    base i j = transport (λ k → B (i ∧ k) (j ∧ k)) a

isProp→isContrPathP : {A : I → Type ℓ} → ((i : I) → isProp (A i))
                    → (x : A i0) (y : A i1) → isContr (PathP A x y)
isProp→isContrPathP ap x y .centre = isProp→PathP ap x y
isProp→isContrPathP ap x y .paths p =
  isProp→SquareP (λ i j → ap j) refl _ _ refl

isSet→SquareP :
  {A : I → I → Type ℓ}
  (isSet : (i j : I) → isSet (A i j))
  → {a : A i0 i0} {b : A i0 i1} {c : A i1 i0} {d : A i1 i1}
  → (p : PathP (λ j → A j i0) a c)
  → (q : PathP (λ j → A i0 j) a b)
  → (s : PathP (λ j → A i1 j) c d)
  → (r : PathP (λ j → A j i1) b d)
  → SquareP A p q s r
isSet→SquareP isset a₀₋ a₁₋ a₋₀ a₋₁ =
  transport (sym (PathP≡Path _ _ _))
            (isHLevelPathP' 1 (isset _ _) _ _ _ _)

-- Has to go through:
_ : ∀ {A : Type} {a b c d : A} (p : a ≡ c) (q : a ≡ b) (s : c ≡ d) (r : b ≡ d)
  → Square p q s r ≡ SquareP (λ _ _ → A) p q s r
_ = λ _ _ _ _ → refl
```
-->
