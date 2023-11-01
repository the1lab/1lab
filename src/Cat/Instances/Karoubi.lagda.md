<!--
```agda
open import Cat.Functor.Equivalence
open import Cat.Functor.Properties
open import Cat.Morphism
open import Cat.Prelude

import Cat.Diagram.Idempotent as CI
```
-->

```agda
module Cat.Instances.Karoubi {o h} (C : Precategory o h) where
```

<!--
```agda
open CI C
import Cat.Reasoning C as C
open C.HLevel-instance
open Precategory
open Functor
```
-->

# Karoubi envelopes

We give a construction of the **Karoubi envelope** $\~\cC$ of a
precategory $\cC$, a formal construction which adds a choice of
splittings for every [idempotent] in $\cC$. Furthermore, the Karoubi
envelope is the _smallest_ idempotent-complete category which admits a
map from $\cC$, in the sense that any $F : \cC \to \cD$ into an
idempotent-complete category $\cD$ factors through $\~\cC$:

$$
\cC \mono \~\cC \to \cD
$$

Furthermore, the `embedding functor`{.Agda ident=Embed} $\cC \to
\~\cC$ is [[fully faithful]].

[idempotent]: Cat.Diagram.Idempotent.html

The `objects` in $\~\cC$ are given by pairs of an object $c : \cC$
and an idempotent $f : c \to c$. A map between $(c,f)$ and $(d,g)$ is
given by a map $\phi : c \to d$ which absorbs $f$ from the left and $g$
from the right: $\phi \circ f = \phi = g \circ \phi$.

```agda
private
  KOb : Type (o ⊔ h)
  KOb = Σ[ c ∈ C.Ob ] Σ[ f ∈ C.Hom c c ] (is-idempotent f)

  KHom : KOb → KOb → Type h
  KHom (c , f , _) (d , g , _) = Σ[ φ ∈ C.Hom c d ] ((φ C.∘ f ≡ φ) × (g C.∘ φ ≡ φ))

  KH≡ : ∀ {a b : C.Ob} {af : C.Hom a a} {bf : C.Hom b b}
          {ai : is-idempotent af} {bi : is-idempotent bf}
          {f g : KHom (a , af , ai) (b , bf , bi)} → fst f ≡ fst g → f ≡ g
  KH≡ = Σ-prop-path (λ _ → hlevel 1)
```

We can see that these data assemble into a precategory. However, note
that the identity on $(c,e)$ in $\~\cC$ _isn't_ the identity in $C$,
it's the chosen idempotent $e$!

```agda
Karoubi : Precategory (o ⊔ h) h
Karoubi .Ob = KOb
Karoubi .Hom = KHom
Karoubi .Hom-set _ _ = hlevel 2

Karoubi .id {x = c , e , i} = e , i , i
Karoubi ._∘_ (f , fp , fp') (g , gp , gp') = f C.∘ g , C.pullr gp , C.pulll fp'

Karoubi .idr {x = _ , _ , i} {_ , _ , j} (f , p , q) = KH≡ {ai = i} {bi = j} p
Karoubi .idl {x = _ , _ , i} {_ , _ , j} (f , p , q) = KH≡ {ai = i} {bi = j} q
Karoubi .assoc {w = _ , _ , i} {z = _ , _ , j} _ _ _ =
  KH≡ {ai = i} {bi = j} (C.assoc _ _ _)
```

We can now define the embedding functor from C to its `Karoubi`{.Agda}
envelope. It has object part $x \mapsto (x, \id)$; The morphism
part of the functor has to send $f : x \to y$ to some $f' : x \to y$
which absorbs $\id$ on either side; But this is just $f$ again.

```agda
Embed : Functor C Karoubi
Embed .F₀ x = x , C.id , id-is-idempotent
Embed .F₁ f = f , C.idr _ , C.idl _
Embed .F-id = KH≡ {ai = id-is-idempotent} {bi = id-is-idempotent} refl
Embed .F-∘ f g = KH≡ {ai = id-is-idempotent} {bi = id-is-idempotent} refl
```

An elementary argument shows that the morphism part of `Embed`{.Agda}
has an inverse given by projecting the first component of the pair;
Hence, `Embed` is `fully faithful`{.Agda ident=is-fully-faithful}.

```agda
Embed-is-fully-faithful : is-fully-faithful Embed
Embed-is-fully-faithful = is-iso→is-equiv $
  iso fst (λ _ → Σ-prop-path (λ _ → hlevel 1) refl) λ _ → refl
```

## Idempotent-completeness

We now show that any idempotent $f : (A, e) \to (A, e)$ admits a
splitting in $\~\cC$. First, note that since $f$ is (by assumption)
idempotent, we have an object given by $(A, f)$; We'll split $f$ as a
map

$$
(A, e) \to (A, f) \to (A, e)
$$

The first map is given by the underlying map of $f : A \to A$. We must
show that $f \circ e = f$, but we have this by the definition of maps in
$\~\cC$. In the other direction, we can _again_ take $f : A \to A$,
which also satisfies $e \circ f = f$.

```agda
is-idempotent-complete-Karoubi : CI.is-idempotent-complete Karoubi
is-idempotent-complete-Karoubi {A = A , e , i} (f , p , q) idem = spl where
  open CI.is-split

  f-idem : f C.∘ f ≡ f
  f-idem i = idem i .fst

  spl : CI.is-split Karoubi (f , p , q)
  spl .F = A , f , f-idem
  spl .project = f , p , f-idem
  spl .inject = f , f-idem , q
```

For this to be a splitting of $f$, we must show that $f \circ f = f$ as
a map $(A, e) \to (A, e)$, which we have by assumption; And we must show
that $f \circ f = \id$ as a map $(A, f) \to (A, f)$. But recall
that the identity on $(A, f)$ is $f$, so we _also_ have this by
assumption!

```agda
  spl .p∘i = KH≡ {ai = f-idem} {bi = f-idem} f-idem
  spl .i∘p = KH≡ {ai = i} {bi = i} f-idem
```

Hence $\~\cC$ is an idempotent-complete category which admits $C$ as
a full subcategory.

If $\cC$ was already idempotent-complete, then `Embed`{.Agda} is an
[[equivalence of categories]] between $\cC$ and $\~\cC$:

```agda
Karoubi-is-completion : is-idempotent-complete → is-equivalence Embed
Karoubi-is-completion complete = ff+split-eso→is-equivalence Embed-is-fully-faithful eso where
  eso : is-split-eso Embed
  eso (c , e , ie) = c' , same where
    open is-split (complete e ie) renaming (F to c'; inject to i; project to p)
    module Karoubi = Cat.Morphism Karoubi
    open Inverses
    same : (c' , C.id , _) Karoubi.≅ (c , e , ie)
    same .to = i , C.idr _ , C.rswizzle (sym i∘p) p∘i
    same .from = p , C.lswizzle (sym i∘p) p∘i , C.idl _
    same .inverses .invl = KH≡ {ai = ie} {bi = ie} i∘p
    same .inverses .invr = KH≡ {ai = id-is-idempotent} {bi = id-is-idempotent} p∘i
```

This makes the Karoubi envelope an "idempotent completion" in two *different* technical
senses^[it is a completion that *adds* splittings of idempotents, and a completion that *is* idempotent]!
