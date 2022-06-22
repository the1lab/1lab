```agda
open import Cat.Prelude

module Cat.Diagram.Coequaliser.Split {o ℓ} (C : Precategory o ℓ) where
open import Cat.Diagram.Coequaliser C
```

<!--
```agda
open import Cat.Reasoning C
private variable
  A B E : Ob
  f g h e s t : Hom A B
```
-->

# Split Coequalizers

Split Coequalizers are one of those definitions that seem utterly opaque when first
presented, but are actually quite natural when viewed through the correct lens.
With this in mind, we are going to provide the motivation _first_, and then
define the general construct.

To start, let $R \subseteq B \times B$ be some equivalence relation. A natural thing
to consider is the quotient $B/R$, which gives us the following diagram:
~~~{.quiver}
\[\begin{tikzcd}
	R & {B \times B} & B & {B/R}
	\arrow[hook, from=1-1, to=1-2]
	\arrow["{p_1}", shift left=2, from=1-2, to=1-3]
	\arrow["{p_2}"', shift right=2, from=1-2, to=1-3]
	\arrow["q", from=1-3, to=1-4]
\end{tikzcd}\]
~~~

Now, when one has a quotient, it's useful to have a means of picking representatives
for each equivalence class. This is essentially what normalization algorithms do,
which we can both agree are very useful indeed. This ends up defining a map
$s : B/R \to B$ that is a section of $q$ (i.e: $q \circ s = id$).

This gives us the following diagram (We've omited the injection of $R$ into
$B \times B$ for clarity).
~~~{.quiver}
\[\begin{tikzcd}
	R & B & {B/R}
	\arrow["q", shift left=2, from=1-2, to=1-3]
	\arrow["s", shift left=2, from=1-3, to=1-2]
	\arrow["{p_1}", shift left=2, from=1-1, to=1-2]
	\arrow["{p_2}"', shift right=2, from=1-1, to=1-2]
\end{tikzcd}\]
~~~

This lets us define yet another map $r : B \to R$, which will witness the fact that
any $b : B$ is related to its representative $s(q(b))$. We can define this map explicitly
as so:
$$
  r(b) = (b, s(q(b)))
$$

Now, how do we encode this diagramatically? To start, $p_1 \circ r = id$ by the
$\beta$ law for products. Furthermore, $p_2 \circ r = s \circ q$, also by the
$\beta$ law for products. This gives us a diagram that captures the essence of having
a quotient by an equivalence relation, along with a means of picking representatives.

~~~{.quiver}
\[\begin{tikzcd}
	R & B & {B/R}
	\arrow["q", shift left=2, from=1-2, to=1-3]
	\arrow["s", shift left=2, from=1-3, to=1-2]
	\arrow["{p_1}", shift left=5, from=1-1, to=1-2]
	\arrow["{p_2}"', shift right=5, from=1-1, to=1-2]
	\arrow["r"', from=1-2, to=1-1]
\end{tikzcd}\]
~~~

Such a situation is called a **split coequaliser**.

```agda
record is-split-coequaliser (f g : Hom A B) (e : Hom B E)
                            (s : Hom E B) (t : Hom B A) : Type (o ⊔ ℓ) where
  field
    coequal : e ∘ f ≡ e ∘ g
    rep-section : e ∘ s ≡ id
    witness-section : f ∘ t ≡ id
    commute : s ∘ e ≡ g ∘ t
```

Now, let's show that this thing actually deserves the name Coequaliser.
```agda
is-split-coequaliser→is-coequalizer :
  is-split-coequaliser f g e s t → is-coequaliser f g e
is-split-coequaliser→is-coequalizer
  {f = f} {g = g} {e = e} {s = s} {t = t} split-coeq =
  coequalizes
  where
    open is-split-coequaliser split-coeq
```

The proof here is mostly a diagram shuffle. We construct the universal
map by going back along $s$, and then following $e'$ to our destination,
like so:

~~~{.quiver}
\[\begin{tikzcd}
	A && B && E \\
	\\
	&&&& X
	\arrow["q", shift left=2, from=1-3, to=1-5]
	\arrow["s", shift left=2, from=1-5, to=1-3]
	\arrow["{p_1}", shift left=5, from=1-1, to=1-3]
	\arrow["{p_2}"', shift right=5, from=1-1, to=1-3]
	\arrow["r"', from=1-3, to=1-1]
	\arrow["{e'}", from=1-3, to=3-5]
	\arrow["{e' \circ s}", color={rgb,255:red,214;green,92;blue,92}, from=1-5, to=3-5]
\end{tikzcd}\]
~~~

```agda
    coequalizes : is-coequaliser f g e
    coequalizes .is-coequaliser.coequal = coequal
    coequalizes .is-coequaliser.coequalise {e′ = e′} _ = e′ ∘ s
    coequalizes .is-coequaliser.universal {e′ = e′} {p = p} =
      (e′ ∘ s) ∘ e ≡⟨ extendr commute ⟩
      (e′ ∘ g) ∘ t ≡˘⟨ p ⟩∘⟨refl ⟩
      (e′ ∘ f) ∘ t ≡⟨ cancelr witness-section ⟩
      e′           ∎
    coequalizes .is-coequaliser.unique {e′ = e′} {p} {colim′} q =
      colim′         ≡⟨ intror rep-section ⟩
      colim′ ∘ e ∘ s ≡⟨ pulll (sym q) ⟩
      e′ ∘ s         ∎
```

Intuitively, we can think of this as constructing a map out of the quotient $B/R$
from a map out of $B$ by picking a representative, and then applying the map out
of $B$. Universality follows by the fact that the representative is related to
the original element of $B$, and uniqueness by the fact that $s$ is a section.

```agda
record Split-coequaliser (f g : Hom A B) : Type (o ⊔ ℓ) where
  field
    {coapex}  : Ob
    coeq      : Hom B coapex
    rep       : Hom coapex B
    witness   : Hom B A
    has-is-split-coeq : is-split-coequaliser f g coeq rep witness

  open is-split-coequaliser has-is-split-coeq public
```

## Split coequalizers and split epimorphisms

Much like the situation with coequalizers, the coequalizing map of a
split coequalizer is a split epimorphism. This follows directly from the fact
that $s$ is a section of $e$.

```agda
is-split-coequaliser→is-split-epic
  : is-split-coequaliser f g e s t → is-split-epic e
is-split-coequaliser→is-split-epic {e = e} {s = s} split-coeq =
  split-epic
  where
    open is-split-epic
    open is-split-coequaliser split-coeq

    split-epic : is-split-epic e
    split-epic .split = s
    split-epic .section = rep-section
```

Also of note, if $e$ is a split epimorphism with splitting $s$, then
the following diagram is a split coequalizer.
~~~{.quiver}
\[\begin{tikzcd}
	A & A & B
	\arrow["id", shift left=3, from=1-1, to=1-2]
	\arrow["{s \circ e}"', shift right=3, from=1-1, to=1-2]
	\arrow["id"{description}, from=1-2, to=1-1]
	\arrow["e", shift left=1, from=1-2, to=1-3]
	\arrow["s", shift left=2, from=1-3, to=1-2]
\end{tikzcd}\]
~~~

Using the intuition that split coequalizers are quotients of equivalence relations
equipped with a choice of representatives, we can decode this diagram as constructing
an equivalence relation on $A$ out of a section of $e$, where $a ~ b$ if and only
if they get taken to the same cross section of $A$ via $s \circ e$.

```agda
is-split-epic→is-split-coequalizer
  : s is-section-of e → is-split-coequaliser id (s ∘ e) e s id
is-split-epic→is-split-coequalizer {s = s} {e = e} section = split-coeq
  where
    open is-split-coequaliser

    split-coeq : is-split-coequaliser id (s ∘ e) e s id
    split-coeq .coequal =
      e ∘ id    ≡⟨ idr e ⟩
      e         ≡⟨ insertl section ⟩
      e ∘ s ∘ e ∎
    split-coeq .rep-section = section
    split-coeq .witness-section = id₂
    split-coeq .commute = sym (idr (s ∘ e))
```
