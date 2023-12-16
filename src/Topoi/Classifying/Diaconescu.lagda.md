<!--
```agda
open import Algebra.Prelude

open import Cat.Functor.Kan.Pointwise
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Limit.Finite
open import Cat.Functor.Kan.Nerve
open import Cat.Diagram.Initial
open import Cat.Instances.Comma

open import Topoi.Base

import Cat.Functor.Reasoning as Functor-kit
import Cat.Reasoning
```
-->

```agda
module Topoi.Classifying.Diaconescu where
```

# Diaconescu's theorem {defines="Diaconescu's-theorem"}

Let $\Sigma$ be a **signature** consisting of sorts $A, B, C\dots$,
function symbols $f, \dots : A \to B$, and  relation symbols $~, \dots$.
We can build a **logical theory** on top of this signature by imposing
**axioms** of the form

$$
P \vdash_{x} Q\text{,}
$$

where $P$ and $Q$ are formulae, and $x$ is a context consisting of
variables typed with sorts from the signature. Depending on the
signature and on what connectives are used to build up the formulae $P$
and $Q$, our logical theory can fit within several frameworks:

- If our formulae can be presented using only $\land$, $\top$, and the
equality relation $=$, then our logic is called **cartesian logic**, and
our theory a **cartesian theory**.

- **Regular logic** is obtained by augmenting cartesian logic with the
quantifier $\exists$.

- **Coherent logic** is obtained by augmenting regular logic with
disjunction $\lor$ and falsity $\bot$.

- **Geometric logic** is obtained by augmenting coherent logic with
_infinitary_ disjunction $\bigvee$.

In addition to the qualifiers above, if our signature has **no** sorts,
then our theory will be called a "propositional theory": A theory built
up of $\land, \bigvee, \top, \bot, \exists$ on a signature with no sorts
is called a **propositional geometric theory**.

Let the contexts of such a theory be denoted by $\mathcal{O}_T$ --- we
see that the entailment relation $x \vdash y$ equips the objects of
$\mathcal{O}_T$ with a [preorder] structure, with the conjunctions
providing meets and the (infinitary) disjunctions providing joins.
Additionally, in this proset, the distributive law

[preorder]: Order.Base.html

$$
x \land \bigvee_i F(i) = \bigvee_i (x \land F(i))
$$

holds. We call such a structure a _frame_, and we can see that that a
frame determines a topological space $X$, by letting the opens of the
topology be the elements of the frame (the points come for free as
filters satisfying a certain condition). This space $X$ can be called
the **classifying space** of the theory $T$, since points of $X$
correspond to models of $T$, and the specialisation preorder on $X$
corresponds to homomorphism of models.

If our theory is _not_ propositional, however, a topological space won't
cut it, since there can be more than one homomorphism between two given
models! Most geometric theories (the theory of groups, the theory of
(local) rings, the theory of fields, the theory of an object) are _not_
propositional, so they won't have useful classifying spaces in this
sense. If we relax the requirement that specialisation be a preorder and
allow a _set_ of model homomorphisms, the structure we get is a category
satisfying certain completeness and exactness properties:

The meets our frame used to have are now [[finite limits]], and the
infinitary disjunctions are [[colimits]]; The infinite distributive law
corresponds to the statement that the [[pullback functors]] preserve
[[colimits]], which follows from the pullback functors having [[right
adjoints]] (i.e. the category is [locally cartesian closed]). Up to a
couple of small omissions[^1], a category satisfying these assumptions
is exactly a **[Grothendieck topos]**, and every topos classifies a
particular theory, in the sense that, letting $G$ and $\cE$ be topoi, a
geometric morphism $G \to \cE$ is equivalent to an $\cE$-model in $G$.

[locally cartesian closed]: Cat.CartesianClosed.Locally.html
[Grothendieck topos]: Topoi.Base.html#grothendieck-topoi

[^1]: [Disjointness of coproducts] and [effectivity of congruences].

[disjointness of coproducts]: Cat.Diagram.Coproduct.Indexed.html#disjoint-coproducts
[effectivity of congruences]: Cat.Diagram.Congruence.html#effective-congruences

That begs a question: What theory do presheaf topoi $\psh(\cC)$
classify? Most presheaf topoi (e.g. the topos of quivers, the topos of
simplicial sets, the topos of sets) are _very far_ from being logically
inspired: Most of those are conceived as being categories of _geometric_
objects! The answer is given by **Diaconescu's theorem**:

> A presheaf topos classifies the flat functors on its site.

A **flat functor** $F : \cC \to \cE$ is one whose [[left Kan extension]]
along the Yoneda embedding $\yo$ (i.e. its [realisation]) is [[left
exact|left exact functor]]. The theorem is almost tautological then:
Letting $F$ be a functor, the nerve-realisation adjunction $\Lan_\yo(F)
\dashv \hom(F(-), -)$ is 75% of the way to being a [geometric morphism],
with flatness _definitionally_ guaranteeing that the [[left adjoint]] is
lex.

[realisation]: Cat.Functor.Kan.Nerve.html
[geometric morphism]: Topoi.Base.html#geometric-morphisms

<!--
```agda
module _ {o κ} {C : Precategory o κ} (𝓣 : Topos κ C) where
  private
    module C = Cat.Reasoning C
    abstract
      colim : is-cocomplete κ κ C
      colim = Topos-is-cocomplete 𝓣
```
-->

```agda
  Flat : {D : Precategory κ κ} → Functor D C → Type _
  Flat F = is-lex (Realisation F colim)

  Diaconescu
    : {D : Precategory κ κ} (F : Functor D C)
    → Flat F
    → Geom[ C , PSh κ D ]
  Inv[ Diaconescu F F-flat ] = Realisation F colim
  Dir[ Diaconescu F F-flat ] = Nerve F
  Diaconescu F F-flat .Inv-lex = F-flat
  Diaconescu F F-flat .Inv⊣Dir = Realisation⊣Nerve F colim
```

Conversely, any given geometric morphism $f : \cC \to \psh(\cD)$
has an inverse image $f^* : \psh(\cD) \to \cC$, which we can turn
into a functor $\cD \to \cC$ by precomposing with the Yoneda
embedding:

```agda
  Diaconescu⁻¹ : ∀ {D : Precategory κ κ} → Geom[ C , PSh κ D ] → Functor D C
  Diaconescu⁻¹ f = Inv[ f ] F∘ よ _
```

A standard fact about the computation of left Kan extensions as colimits
tells us that any functor (flat or not) $F : \cD \to \cC$ can be
recovered as the composite $\Lan_\yo(F) \circ \yo$, because $\yo$ is a
[[fully faithful]] functor.

<!--
```
  module _ {D : Precategory κ κ} (F : Functor D C) (flat : Flat F) where
    private module DC = Cat.Reasoning Cat[ D , C ]
```
-->

```agda
    Diaconescu-invl : Diaconescu⁻¹ (Diaconescu F flat) DC.≅ F
    Diaconescu-invl = ff→cocomplete-lan-ext (よ D) F colim (よ-is-fully-faithful D)
```
