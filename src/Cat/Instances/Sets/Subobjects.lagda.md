<!--
```agda
open import Cat.Displayed.Instances.Subobjects
open import Cat.Diagram.Pullback.Properties
open import Cat.Instances.Sets.Complete
open import Cat.Diagram.Subobject
open import Cat.Diagram.Pullback
open import Cat.Instances.Sets
open import Cat.Prelude
```
-->

```agda
module Cat.Instances.Sets.Subobjects where
```

# Sets has a subobject classifier

This module proves that the category of sets has a [[subobject
classifier]], or, more specifically, that the "constantly true" function
$\top \to \Omega$ is a [[generic subobject]] in the category of sets.
The idea of the proof is straightforward, since the subobjects in
$\Sets$ correspond to the [[embeddings]], and the general logic of [[map
classifiers]] applies, so there is an equivalence between $A \to \Omega$
and $\Sigma_B B \mono A$.

<!--
```agda
private module gen = is-generic-subobject
private module So = Subobject-classifier
open is-pullback
```
-->

However, we still have to put in a bit of effort to connect this idea to
the actual universal property. We'll need a pair of helper lemmas. The
first is immediate, since it's just writing down the aforementioned
connection between subobjects in $\Sets$ and embeddings into their
codomains:

```agda
Sets-subobject-is-embedding
  : ∀ {ℓ} {X : Set ℓ}
  → (m : Subobject (Sets ℓ) X)
  → is-embedding (m .map)
Sets-subobject-is-embedding {X = X} m = monic→is-embedding (X .is-tr) λ {C} →
  m .monic {C}
```

The second lemma is slightly more involved. It connects the
[[pullbacks]] in $\Sets$, where one corner is terminal, with the direct
type-theoretic definition of `fibre`{.Agda}. The type is a bit involved
for silly formalisation reasons, so let's get it out of the way first,
and explain it after the noise.

```agda
Sets-pullback-fibre
  : ∀ {ℓ} {A B T F : Set ℓ} {m : ∣ F ∣ → ∣ A ∣} {f : ∣ A ∣ → ∣ B ∣} {x : ∣ B ∣}
  → ⦃ _ : H-Level ∣ T ∣ 0 ⦄
  → is-pullback (Sets _) {A} {B} {T} {F} m f (λ _ → hlevel 0 .centre) (λ _ → x)
  → (f : fibre f x)
  → fibre m (f .fst)
```

<details note>
<summary>If you're interested in formalisation, this `<details>`{.html}
tag explains why the type of `Sets-pullback-fibre`{.Agda} is so
noisy.</summary>

The crux of the issue is that a `Set`{.Agda} is not merely a type, but a
pair consisting of a type and a proof of its [[setness|set]]. Even
though the proof is essentially unique (since being a set is a
[[proposition]]), there might be different proofs up to definitional
equality, and Agda can not determine which proof we meant based simply
on the underlying type. Since a function between sets only mentions the
underlying type, every time we have something like `is-pullback`{.Agda},
we have to specify the sets explicitly, hence the long application
`is-pullback (Sets _) {A} {B} {T} {F}`.

For the same reason, we allow different "terminal objects", too: rather
than explicitly mentioning the type `⊤`{.Agda}, we can ask for any set
whose underlying type is [[contractible]]; That gives us a canonical
choice of point to use in the pullback square.

<!--
```agda
_ = ⊤
```
-->

</details>

~~~{.quiver .short-05}
\[\begin{tikzcd}[ampersand replacement=\&]
	F \&\& \top \\
	\\
	A \&\& B
	\arrow["f"', from=3-1, to=3-3]
	\arrow["p", from=1-3, to=3-3]
	\arrow["{!}", from=1-1, to=1-3]
	\arrow["m"', from=1-1, to=3-1]
	\arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=3-3]
\end{tikzcd}\]
~~~

We're given an arbitrary pullback square, as in the diagram above. The
lemma says that, given an element $y : A$ satisfying $f(y) = p$, i.e. a
point of the fibre $f^*(p)$, there is a corresponding point in the fibre
$m^*(y)$.

```agda
Sets-pullback-fibre {f = f} {x} pb it = _ , prf $ₚ it where
```

<!--
```agda
  module pb = is-pullback pb
  P : Set _
  ∣ P ∣ = fibre f x
  P .is-tr = hlevel!
```
-->

The proof is remarkably straightforward. The fibre $f^*(p)$ fits in the
diagram above as

~~~{.quiver .tall-1}
\[\begin{tikzcd}[ampersand replacement=\&]
  {f^*(p)} \\
  \& F \&\& \top \\
  \\
  \& A \&\& B
  \arrow["f"', from=4-2, to=4-4]
  \arrow["p", from=2-4, to=4-4]
  \arrow["{!}", from=2-2, to=2-4]
  \arrow["m"', from=2-2, to=4-2]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=2-2, to=4-4]
  \arrow["{\pi_1}"{description}, curve={height=12pt}, from=1-1, to=4-2]
  \arrow[curve={height=-12pt}, from=1-1, to=2-4]
  \arrow[dashed, "{\exists! g}"', from=1-1, to=2-2]
\end{tikzcd}\]
~~~

so that there exists a (unique) function fitting into the indicated,
dashed line. Commutativity of the diagram ensures that $m(g(y)) = y$, so
that we indeed map $y : f^*(x)$ to $g(y) : m^*(y)$.

```agda
  prf = pb.p₁∘universal {P}
    {p₂' = λ _ → hlevel 0 .centre}
    {p = funext λ a → a .snd}
```

We're ready to put the proof together. The subobject classifier is, of
course, the type of propositions $\Omega$, and the generic subobject is
the aforementioned "constantly true" arrow.

```agda
Sets-subobject-classifier : ∀ {ℓ} → Subobject-classifier (Sets ℓ) Sets-terminal
Sets-subobject-classifier .So.Ω = soc where
  soc : Set _
  ∣ soc ∣ = Lift _ Ω
  soc .is-tr = hlevel 2

Sets-subobject-classifier .So.true _ = lift (el ⊤ (hlevel 1))
Sets-subobject-classifier .So.generic = isg where
```

Given a set $X$ and a subobject $m : A \mono X$, we obtain a mapping
$\name{m} : X \to \Omega$ through the function $x \mapsto m^*(x)$. By
the very definition of being an embedding, all these fibres are
propositions.

```agda
  module _ {X : Set _} (m : Subobject (Sets _) X) where
    name : ∣ X ∣ → Lift _ Ω
    name x = lift (elΩ (fibre (m .map) x))

    out-name : ∀ {x} → x ∈ name → x ∈ fibre (m .map)
    out-name = out! {pa = Sets-subobject-is-embedding m _}
```

We must now show that the pullback of the true arrow along $\name{m}$ is
$m$, as in the square below.

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  A \&\& 1 \\
  \\
  X \&\& \Omega
  \arrow["m"', from=1-1, to=3-1]
  \arrow["{\name{m}}"', from=3-1, to=3-3]
  \arrow["{\rm{true}}", from=1-3, to=3-3]
  \arrow[from=1-1, to=1-3]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=3-3]
\end{tikzcd}\]
~~~

Commutativity of the square follows at once, since any inhabited
proposition is equal to the true proposition, and the fibre $m^*(mx)$ is
inhabited by $(x, \refl)$. If we're given $p : P \to X$ such that
$\name{m} \circ p = \rm{true}$, we define a function $p' : P \to A$ by
the following rule. Given $x : P$, we have the assumption $px \in
\name{m}$, i.e. some element $e : m^*(px)$, from which $p'$ can project
its $A$. The commutativity condition $mp'(x) = px$ follows from
projecting the proof out of this same $e$.

```agda
  isg : is-generic-subobject (Sets _) Sets-terminal _
  isg .gen.name = name
  isg .gen.classifies m .square = funext λ x → ap lift (to-is-true (inc (_ , refl)))
  isg .gen.classifies m .universal prf p = out-name m (from-is-true (prf $ₚ p)) .fst
  isg .gen.classifies m .p₁∘universal {p = prf} = funext λ p →
    out-name m (from-is-true (prf $ₚ p)) .snd
  isg .gen.classifies m .p₂∘universal = refl
```

To show uniqueness of $p'$, recall that that $m$ is injective, so that
if $q : P \to A$ also satisfies $mq = p$, we must have $mq(x) = px =
mp'(x)$, hence $q = p'$.

```agda
  isg .gen.classifies {X = X} m .unique {p = prf} q _ = funext λ x →
    ap fst (Sets-subobject-is-embedding m _
      (_ , q $ₚ x)
      (_ , out-name m (from-is-true (prf $ₚ x)) .snd))
```

The final step is uniqueness of $\name{m}$ itself. So suppose we have $n
: X \to \Omega$ such that $n^*(\rm{true})$ is also $m$, i.e. it also
fits as the bottom arrow in the pullback diagram above. Since we're
comparing functions into $\Omega$, it will suffice to show pointwise
bi-implication.

In one direction, we assume $i : x \in n$ and must produce an element in
the fibre $m^*(x)$. By the previous `lemma about pullbacks`{.Agda
ident=Sets-pullback-fibre}, producing $(x, i) : n^*(\rm{true})$ suffices.

```agda
  isg .gen.unique {m = m} {nm = n} pb = funext λ x → ap lift (Ω-ua
    (λ it → inc (Sets-pullback-fibre pb (x , ap lift (to-is-true it))))
```

In the converse direction, we have $i : x \in \name{m}$, and have to
show $x \in n$. Split this into $(e, p) : m^*(x)$. We then have $me \in
n$ since $n$ also names $m$, and transport along $p : me = x$ finishes
the proof.

```agda
    (λ it →
      let
        (elt , prf) = out-name m it
      in subst ⌞_⌟ (ap n prf) (from-is-true (is-pullback.square pb $ₚ elt))))
```
