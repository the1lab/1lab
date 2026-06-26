<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Instances.Localisation
open import Cat.Diagram.Colimit.Base
open import Cat.Functor.Adjoint.Hom
open import Cat.Functor.Properties
open import Cat.Instances.Discrete
open import Cat.Diagram.Terminal
open import Cat.Functor.Constant
open import Cat.Functor.Adjoint
open import Cat.Instances.Comma
open import Cat.Connected
open import Cat.Groupoid
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Reasoning as Cr

open is-connected-groupoid
open Precategory
open Congruence
open Functor
open _=>_
open ↓Obj
open ↓Hom
```
-->

```agda
module Cat.Functor.Final where
```

# Final functors {defines="final-functor"}

A **final functor** expresses an equivalence of diagram schemata for the
purposes of computing colimits: if $F : \cC \to \cD$ is final,
then colimits for $D : \cD \to \cE$ are equivalent to colimits
for $D\circ F : \cC \to \cE$. A terminological warning: in older
literature (e.g. [@Borceux:vol1] and [@AdamekRosicky]), these functors
are called **cofinal**, but we stick with terminology from the nLab
here.

<!--
```agda
module
  _ {o ℓ o' ℓ'} {𝒞 : Precategory o ℓ} {𝒟 : Precategory o' ℓ'}
    (F : Functor 𝒞 𝒟)
  where

  open Functor

  private
    module 𝒞 = Cr 𝒞
    module 𝒟 = Cr 𝒟
    module F = Functor F
```
-->

Finality has an elementary characterisation: we define a functor $F$ to
be final if, for every $d$, the comma category $d \swarrow F$ is
[[connected|connected category]]. That is, unpacking, the following data:
for every object $d : \cD$, an object $d_0$ and a map $d_! : d \to F(d_0)$,
and for every span

~~~{.quiver}
\[\begin{tikzcd}
  & d \\
  Fa && Fb\text{,}
  \arrow["f", from=1-2, to=2-1]
  \arrow["g"', from=1-2, to=2-3]
\end{tikzcd}\]
~~~

a finite [[zigzag]] of morphisms from $a$ to $b$, inducing a chain of commuting
triangles from $f$ to $g$. For example, in the case of a "cospan" zigzag
$a \rightarrow a_0 \leftarrow b$:

~~~{.quiver}
\[\begin{tikzcd}
  & d \\
  Fa & {Fa_0} & Fb
  \arrow["f"', from=1-2, to=2-1]
  \arrow[from=2-1, to=2-2]
  \arrow[from=2-3, to=2-2]
  \arrow["g", from=1-2, to=2-3]
  \arrow["{f_0}"{description}, from=1-2, to=2-2]
\end{tikzcd}\]
~~~

```agda
  is-final : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ')
  is-final = ∀ d → is-connected-cat (d ↙ F)
```

<!--
```agda
  module is-final (fin : is-final) (d : 𝒟.Ob) = is-connected-groupoid (fin d)

  module
    _ {o'' ℓ''} {ℰ : Precategory o'' ℓ''} {D : Functor 𝒟 ℰ} (final : is-final)
    where
    private
      module fin = is-final final
      module D = Func D
      module ℰ = Cr ℰ
```
-->

The utility of this definition comes, as mentioned, from the ability to
move (colimiting) cocones back and forth between a diagram $D$ and its
restriction $D_{|F}$ to the domain category $\cC$. If we have a cocone
$\kappa : \{DF(d) \to K\}$, then precomposition with the map $D(d_!) :
D(d) \to DF(d_0)$ (where $d_! : d \to F(d_0)$ comes from the finality of
$F$) defines a cocone $\{D(d) \to K\}$.

However, since the comma category $d \swarrow F$ is *merely* inhabited,
we need to make sure that this extension is independent of the choice of
$d_0$ and $d_!$.  This follows from naturality of the cocone and by
connectedness of $d \swarrow F$, as expressed by the commutativity of
the following diagram:

~~~{.quiver .tall-1}
\[\begin{tikzcd}
  & DFa \\
  Dd && K \\
  & DFb
  \arrow["Df", from=2-1, to=1-2]
  \arrow["{\kappa_a}", from=1-2, to=2-3]
  \arrow["Dg"', from=2-1, to=3-2]
  \arrow["{\kappa_b}"', from=3-2, to=2-3]
  \arrow["DFh"{description}, from=1-2, to=3-2]
\end{tikzcd}\]
~~~

```agda
    module _ {coapex} (cone : D F∘ F => Const coapex) where
      extend : ∀ d → Ob (d ↙ F) → ℰ.Hom (D.₀ d) coapex
      extend d f = cone .η (f .cod) ℰ.∘ D.₁ (f .map)

      opaque
        extend-const1
          : ∀ d {f g : Ob (d ↙ F)} (h : ↓Hom _ _ f g)
          → extend d f ≡ extend d g
        extend-const1 d {f} {g} h =
          cone .η _ ℰ.∘ D.₁ (f .map)                          ≡˘⟨ cone .is-natural _ _ _ ∙ ℰ.idl _ ℰ.⟩∘⟨refl ⟩
          (cone .η _ ℰ.∘ D.₁ (F.₁ (h .bot))) ℰ.∘ D.₁ (f .map) ≡⟨ D.pullr refl ⟩
          cone .η _ ℰ.∘ D.₁ ⌜ F.₁ (h .bot) 𝒟.∘ f .map ⌝       ≡⟨ ap! (sym (h .com) ∙ 𝒟.idr _) ⟩
          cone .η _ ℰ.∘ D.₁ (g .map)                          ∎

      opaque
        extend-const
          : ∀ d (f g : Ob (d ↙ F))
          → extend d f ≡ extend d g
        extend-const d f g = case fin.path d f g of
          Meander-rec-≡ (el! _) (extend d) (extend-const1 d)
```

In order to make reasoning easier, we define the extended cocone
simultaneously with an elimination principle for its components.

```agda
      extend-cocone : D => Const coapex
      extend-cocone-elim
        : ∀ d {ℓ} (P : ℰ.Hom (D.₀ d) coapex → Type ℓ)
        → (∀ f → is-prop (P f))
        → (∀ f → P (extend d f))
        → P (extend-cocone .η d)

      extend-cocone .η d = ∥-∥-rec-set (hlevel 2)
        (extend d) (extend-const d) (fin.point d)

      extend-cocone .is-natural x y f = extend-cocone-elim x
        (λ ex → extend-cocone .η y ℰ.∘ D.₁ f ≡ ex)
        (λ _ → hlevel 1)
        (λ ex → extend-cocone-elim y
          (λ ey → ey ℰ.∘ D.₁ f ≡ extend x ex)
          (λ _ → hlevel 1)
          λ ey → ℰ.pullr (sym (D.F-∘ _ _))
               ∙ sym (extend-const x ex (↓obj (ey .map 𝒟.∘ f))))
        ∙ sym (ℰ.idl _)
```

<!--
```agda
      extend-cocone-elim d P prop h = ∥-∥-elim
        {P = λ f → P (∥-∥-rec-set (hlevel 2) (extend d) (extend-const d) f)}
        (λ _ → prop _) h (fin.point d)
```
-->

In the other direction, suppose that we have a cocone $\{D(x) \to K\}$
--- inserting $F$ in the appropriate places makes a cocone $\{DF(x) \to
K\}$.

```agda
    restrict-cocone : ∀ {coapex} → D => Const coapex → D F∘ F => Const coapex
    restrict-cocone K .η x = K .η (F.₀ x)
    restrict-cocone K .is-natural x y f = K .is-natural (F.₀ x) (F.₀ y) (F.₁ f)
```

A computation using connectedness of the comma categories shows that
these formulae are mutually inverse:

```agda
    open is-iso
    extend-cocone-is-iso : ∀ {coapex} → is-iso (extend-cocone {coapex})
    extend-cocone-is-iso .from = restrict-cocone
    extend-cocone-is-iso .rinv K = ext λ o →
      extend-cocone-elim (restrict-cocone K) o
        (λ ex → ex ≡ K .η o)
        (λ _ → hlevel 1)
        λ _ → K .is-natural _ _ _ ∙ ℰ.idl _
    extend-cocone-is-iso .linv K = ext λ o →
      extend-cocone-elim K (F.₀ o)
        (λ ex → ex ≡ K .η o)
        (λ _ → hlevel 1)
        λ f → extend-const K (F.₀ o) f (↓obj 𝒟.id) ∙ D.elimr refl
```

The most important conclusion that we get is the following: If you can
show that the restricted cocone is a colimit, then the original cocone
was a colimit, too! We'll do this in two steps: first, show that the
_extension_ of a colimiting cocone is a colimit. Then, using the fact
that `restrict-cocone`{.Agda} is an equivalence, we'll be able to fix up
the polarity mismatch.

```agda
    extend-is-colimit
      : ∀ {coapex} (K : D F∘ F => Const coapex)
      → is-colimit (D F∘ F) coapex K
      → is-colimit D coapex (extend-cocone K)
```

<details>
<summary>
The proof of the auxiliary lemma is a direct computation, so we'll leave
it in this `<details>`{.html} tag for the curious reader only.
</summary>

```agda
    extend-is-colimit {coapex} K colim =
      to-is-colimitp mc refl
      module extend-is-colimit where
        module colim = is-colimit colim
        open make-is-colimit

        mc : make-is-colimit D coapex
        mc .ψ x = extend-cocone K .η x
        mc .commutes f = extend-cocone K .is-natural _ _ _ ∙ ℰ.idl _
        mc .universal eta p =
          colim.universal (λ j → eta (F.₀ j)) λ f → p (F.₁ f)
        mc .factors {j} eta p =
          extend-cocone-elim K j
            (λ ex → mc .universal eta p ℰ.∘ ex ≡ eta j)
            (λ _ → hlevel 1)
            λ f → ℰ.pulll (colim.factors _ _) ∙ p (f .map)
        mc .unique eta p other q =
          colim.unique _ _ _ λ j →
            sym (ℰ.refl⟩∘⟨ extend-cocone-is-iso .linv K ηₚ j)
            ∙ q (F.₀ j)
```

</details>

```agda
    is-colimit-restrict
      : ∀ {coapex}
      → (K : D => Const coapex)
      → is-colimit (D F∘ F) coapex (restrict-cocone K)
      → is-colimit D coapex K
    is-colimit-restrict {coapex} K colim =
      to-is-colimitp
        (extend-is-colimit.mc (restrict-cocone K) colim)
        (extend-cocone-is-iso .rinv K ηₚ _)
        where open is-iso
```

## Examples

Final functors between [[pregroupoids]] have a very simple
characterisation: they are the [[full|full functor]], [[essentially
surjective]] functors.  In this case, there is a direct connection with
homotopy type theory: groupoids are 1-types, comma categories $d
\swarrow F$ are [[fibres]] of $F$ over $d$, and so finality says that
$F$ is a [[connected map]].

Essential surjectivity on objects pretty much exactly says that each
comma category $d \swarrow F$ is inhabited.  To see that fullness
implies the existence of zigzags, meditate on the following diagram:

~~~{.quiver}
\[\begin{tikzcd}
  & d \\
  Fx && Fy
  \arrow["f"', from=1-2, to=2-1]
  \arrow["g", from=1-2, to=2-3]
  \arrow["{g \circ f\inv = F(z)}"', from=2-1, to=2-3]
\end{tikzcd}\]
~~~

```agda
  module _ (𝒞-grpd : is-pregroupoid 𝒞) (𝒟-grpd : is-pregroupoid 𝒟) where
    full+eso→final : is-full F → is-eso F → is-final
    full+eso→final full eso d .path f g = do
      z , p ← full (g .map 𝒟.∘ 𝒟-grpd (f .map) .inv)
      pure $ zig
        (↓hom {bot = z}
          (𝒟.idr _ ∙ sym (𝒟.rswizzle p (𝒟-grpd (f .map) .invr))))
        []
      where open 𝒟.is-invertible
    full+eso→final full eso d .point =
      ∥-∥-map (λ e → ↓obj (𝒟.from (e .snd))) (eso d)
```

For the other direction, given $f : Fx \to Fy$, observe that
connectedness of the comma category $Fx \swarrow F$ gives us a zigzag
between $x$ and $y$, but since $\cC$ is a pregroupoid we can evaluate
this zigzag to a single morphism $z : x \to y$ such that $Fz = f$.

```agda
    final→full+eso : is-final → is-full F × is-eso F
    final→full+eso fin .fst {x} {y} f = do
      zs ← fin (F.₀ x) .path (↓obj 𝒟.id) (↓obj f)
      let z = Free-groupoid-counit
            (↓-is-pregroupoid _ _ ⊤Cat-is-pregroupoid 𝒞-grpd)
            .F₁ zs
      pure (z .bot , sym (𝒟.idr _) ∙ sym (z .com) ∙ 𝒟.idr _)
    final→full+eso fin .snd d = do
      fd ← fin d .point
      pure (fd .cod , 𝒟.invertible→iso (fd .map) (𝒟-grpd _) 𝒟.Iso⁻¹)
```

Another general class of final functors is given by [[right adjoint]]
functors. This follows directly from the characterisation of right
adjoints in terms of [[free objects]]: since the comma categories $c
\swarrow R$ have initial objects, they are connected.

```agda
right-adjoint-is-final
  : ∀ {o ℓ o' ℓ'} {𝒞 : Precategory o ℓ} {𝒟 : Precategory o' ℓ'}
  → {L : Functor 𝒞 𝒟} {R : Functor 𝒟 𝒞} (L⊣R : L ⊣ R)
  → is-final R
right-adjoint-is-final L⊣R c =
  initial→connected (left-adjoint→universal-maps L⊣R c)
```

In particular, the inclusion of a [[terminal object]] into a category is
a final functor. This means that the colimit of any diagram over a shape
category with a terminal object is simply the value of the diagram on
the terminal object.

```agda
terminal→inclusion-is-final
  : ∀ {o ℓ} {𝒞 : Precategory o ℓ}
  → (top : 𝒞 .Ob) (term : is-terminal 𝒞 top)
  → is-final (!Const {C = 𝒞} top)
terminal→inclusion-is-final top term = right-adjoint-is-final
  (is-terminal→inclusion-is-right-adjoint _ top term)
```

## Closure under composition

<!--
```agda
module
  _ {o ℓ o' ℓ' o'' ℓ''}
    {𝒞 : Precategory o ℓ} {𝒟 : Precategory o' ℓ'} {ℰ : Precategory o'' ℓ''}
    (F : Functor 𝒞 𝒟) (G : Functor 𝒟 ℰ)
    (f-fin : is-final F) (g-fin : is-final G)
  where
  private
    module 𝒟 = Cr 𝒟
    module ℰ = Cr ℰ
    module G = Func G
    module F = Functor F
    module ff = is-final F f-fin
    module gf = is-final G g-fin
  open ↙-compose F G
```
-->

We now prove that final functors are closed under composition.

First, given an object $c : \cC$ we get a map $g : c \to Gc_0$ using the
finality of $G$ and a map $f : c_0 \to Fc_1$ using the finality of $F$,
which we can compose into an object of $c \swarrow G \circ F$.

```agda
  F∘-is-final : is-final (G F∘ F)
  F∘-is-final c .point = do
    g ← gf.point c
    f ← ff.point (g .cod)
    pure (g ↙> f)
```

Now, given a span $GFx \leftarrow c \rightarrow GFy$, finality of $G$
gives us a zigzag between $Fx$ and $Fy$ in $c \swarrow G$, but we need a
zigzag between $x$ and $y$ in $c \swarrow G \circ F$.  Thus we have to
`refine`{.Agda} our zigzag step by step, using the finality of $F$.

```agda
  F∘-is-final c .path f g = do
    gz ← gf.path c (↓obj (f .map)) (↓obj (g .map))
    fz ← refine gz (↓obj 𝒟.id) (↓obj 𝒟.id)
    pure (subst₂ (Meander (c ↙ G F∘ F)) ↙>-id ↙>-id fz)
```

We start by defining a [[congruence]] on the objects of $c \swarrow G$,
whereby $f : c \to Gx$ and $g : c \to Gy$ are related if, for any
extensions $f' : x \swarrow F$ and $g' : y \swarrow F$, there merely
exists a zigzag between the corresponding objects of $c \swarrow G \circ
F$:

~~~{.quiver}
\[\begin{tikzcd}
  & c \\
  Gx && Gy \\
  {GFx'} && {GFy'}
  \arrow["f", from=1-2, to=2-1]
  \arrow["g"', from=1-2, to=2-3]
  \arrow[from=2-1, to=3-1]
  \arrow[from=2-3, to=3-3]
  \arrow[squiggly, tail reversed, from=3-1, to=3-3]
\end{tikzcd}\]
~~~

```agda
    where
      R : Congruence (Ob (c ↙ G)) _
      R ._∼_ f g =
        ∀ (f' : Ob (f .cod ↙ F)) (g' : Ob (g .cod ↙ F))
        → ∥ Meander (c ↙ G F∘ F) (f ↙> f') (g ↙> g') ∥
      R .has-is-prop _ _ = hlevel 1
```

That this is a congruence is easily checked using the finality of $F$.

```agda
      R .reflᶜ {f} f' g' =
        Free-groupoid-map (↙-compose f) .F₁ <$> ff.path (f .cod) f' g'
      R ._∙ᶜ_ {f} {g} {h} fg gh f' h' = do
        g' ← ff.point (g .cod)
        ∥-∥-map₂ _++_ (gh g' h') (fg f' g')
      R .symᶜ fg g' f' = ∥-∥-map (reverse _) (fg f' g')
```

Using the universal mapping property of the free groupoid into
congruences, we conclude by showing that any two arrows connected by a
morphism are related, which again involves the connectedness of $x
\swarrow F$.

```agda
      refine1 : ∀ {f g} → Hom (c ↙ G) f g → R ._∼_ f g
      refine1 {f} {g} h f' g' = do
        z ← ff.path (f .cod) f' (↓obj (g' .map 𝒟.∘ h .bot))
        let
          z' : Meander (c ↙ G F∘ F) _ _
          z' = Free-groupoid-map (↙-compose f) .F₁ z
          fixup : f ↙> ↓obj (g' .map 𝒟.∘ h .bot) ≡ g ↙> g'
          fixup = ext $ refl ,ₚ G.pushl refl ∙ (ℰ.refl⟩∘⟨ sym (h .com) ∙ ℰ.idr _)
        pure (subst (Meander (c ↙ G F∘ F) (f ↙> f')) fixup z')

      refine : ∀ {f g} → Meander (c ↙ G) f g → R ._∼_ f g
      refine = Meander-rec-congruence R refine1
```
