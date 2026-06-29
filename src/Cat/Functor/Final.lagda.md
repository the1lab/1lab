<!--
```agda
open import Cat.Functor.Properties.FullyFaithful
open import Cat.Functor.Adjoint.Continuous
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Colimit.Cocone
open import Cat.Instances.Localisation
open import Cat.Diagram.Colimit.Base
open import Cat.Functor.Adjoint.Hom
open import Cat.Functor.Equivalence
open import Cat.Functor.Properties
open import Cat.Instances.Discrete
open import Cat.Diagram.Terminal
open import Cat.Functor.Constant
open import Cat.Functor.Kan.Base
open import Cat.Diagram.Initial
open import Cat.Functor.Adjoint
open import Cat.Instances.Comma
open import Cat.Connected
open import Cat.Groupoid
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Reasoning as Cr

open is-connected-groupoid
open is-precat-iso
open Precategory
open Cocone-hom
open Congruence
open Functor
open is-iso
open Cocone
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
purposes of computing [[colimits]]: if $F : \cC \to \cD$ is final,
then colimits for $D : \cD \to \cE$ are equivalent to colimits
for $D F : \cC \to \cE$. A terminological warning: in older
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
    _ {o'' ℓ''} {ℰ : Precategory o'' ℓ''} (D : Functor 𝒟 ℰ)
    where
```
-->

The utility of this definition comes, as mentioned, from the ability to
move cocones back and forth between a diagram $D$ and its restriction
$D F$ to the domain category $\cC$, in a way that preserves the
property of being a [[colimit]]. First, for any functor $F$, we can
restrict cocones under $D$ to cocones under $D F$ by precomposition.

```agda
    restrict-cocone : ∀ {coapex} → D => Const coapex → D F∘ F => Const coapex
    restrict-cocone K .η x = K .η (F.₀ x)
    restrict-cocone K .is-natural x y f = K .is-natural (F.₀ x) (F.₀ y) (F.₁ f)

    Restrict-cocone : Functor (Cocones D) (Cocones (D F∘ F))
    Restrict-cocone .F₀ K = cocone→Cocone _ (restrict-cocone (Cocone→cocone _ K))
    Restrict-cocone .F₁ f .map = f .map
    Restrict-cocone .F₁ f .com c = f .com (F.₀ c)
    Restrict-cocone .F-id = ext refl
    Restrict-cocone .F-∘ _ _ = ext refl
```

<!--
```agda
  module
    _ {o'' ℓ''} {ℰ : Precategory o'' ℓ''} {D : Functor 𝒟 ℰ} (final : is-final)
    where
    private
      module fin = is-final final
      module D = Func D
      module ℰ = Cr ℰ
```
-->

The point is now that, if $F$ is final, then the restriction functor
thus defined is an [[equivalence of categories]] between the categories
of cocones under $D$ and $D F$.

First, if we have a cocone
$\kappa : \{DF(d) \to K\}$, then precomposition with the map $D(d_!) :
D(d) \to DF(d_0)$ (where $d_! : d \to F(d_0)$ comes from the finality of
$F$) defines a cocone $\{D(d) \to K\}$.

However, since the comma category $d \swarrow F$ is *merely* inhabited,
we need to make sure that this extension is independent of the choice of
$d_0$ and $d_!$. This follows from naturality of the cocone and by
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
    module _ {coapex} (cocone : D F∘ F => Const coapex) where
      extend : ∀ d → Ob (d ↙ F) → ℰ.Hom (D.₀ d) coapex
      extend d f = cocone .η (f .cod) ℰ.∘ D.₁ (f .map)

      opaque
        extend-const1
          : ∀ d {f g : Ob (d ↙ F)} (h : ↓Hom _ _ f g)
          → extend d f ≡ extend d g
        extend-const1 d {f} {g} h =
          cocone .η _ ℰ.∘ D.₁ (f .map)                          ≡˘⟨ cocone .is-natural _ _ _ ∙ ℰ.idl _ ℰ.⟩∘⟨refl ⟩
          (cocone .η _ ℰ.∘ D.₁ (F.₁ (h .bot))) ℰ.∘ D.₁ (f .map) ≡⟨ D.pullr refl ⟩
          cocone .η _ ℰ.∘ D.₁ ⌜ F.₁ (h .bot) 𝒟.∘ f .map ⌝       ≡⟨ ap! (sym (h .com) ∙ 𝒟.idr _) ⟩
          cocone .η _ ℰ.∘ D.₁ (g .map)                          ∎

      opaque
        extend-const
          : ∀ d (f g : Ob (d ↙ F))
          → extend d f ≡ extend d g
        extend-const d f g = case fin.path d f g of
          Meander-rec-≡ (el! _) (extend d) (extend-const1 d)

      extend' : ∀ d → ∥ Ob (d ↙ F) ∥ → ℰ.Hom (D.₀ d) coapex
      extend' d = ∥-∥-rec-set (hlevel 2) (extend d) (extend-const d)

      extend-cocone : D => Const coapex
      extend-cocone .η d = extend' d (fin.point d)
      extend-cocone .is-natural x y f =
        case fin.point x , fin.point y return
          (λ (x' , y') → extend' y y' ℰ.∘ D.₁ f ≡ ℰ.id ℰ.∘ extend' x x')
        of λ x' y' →
          extend y y' ℰ.∘ D.₁ f           ≡⟨ D.pullr refl ⟩
          extend x (↓obj (y' .map 𝒟.∘ f)) ≡⟨ extend-const x (↓obj _) x' ⟩
          extend x x'                     ≡⟨ ℰ.introl refl ⟩
          ℰ.id ℰ.∘ extend x x'            ∎
```

A few more computations show that `restrict-cocone`{.Agda} and
`extend-cocone`{.Agda} are inverses (so that `Restrict-cocone`{.Agda}
is an equivalence on objects), and that the restriction functor is
fully faithful, which makes it an isomorphism of categories (and thus
an equivalence).

```agda
    restrict-cocone-is-equiv : ∀ {coapex} → is-equiv (restrict-cocone D {coapex = coapex})
    restrict-cocone-is-equiv = is-iso→is-equiv λ where
      .from K → extend-cocone K
      .rinv K → ext λ c →
        case fin.point (F.₀ c) return
          (λ c' → extend' _ (F.₀ c) c' ≡ K .η c)
        of λ c' →
          extend-const K (F.₀ c) c' (↓obj 𝒟.id) ∙ D.elimr refl
      .linv K → ext λ d →
        case fin.point d return
          (λ d' → extend' (restrict-cocone D K) d d' ≡ K .η d)
        of λ d' →
          K .is-natural _ _ (d' .map) ∙ ℰ.eliml refl

    restrict-cocone≃ : ∀ {coapex} → (D => Const coapex) ≃ (D F∘ F => Const coapex)
    restrict-cocone≃ = _ , restrict-cocone-is-equiv

    Restrict-cocone-ff : is-fully-faithful (Restrict-cocone D)
    Restrict-cocone-ff {X} {Y} = is-iso→is-equiv λ where
      .is-iso.from f .map → f .map
      .is-iso.from f .com d → case fin.point d of λ d' →
        f .map ℰ.∘ X .ψ d                                 ≡⟨ ℰ.cdr (sym (X .commutes (d' .map))) ⟩
        f .map ℰ.∘ X .ψ (F.₀ (d' .cod)) ℰ.∘ D.₁ (d' .map) ≡⟨ ℰ.pulll (f .com (d' .cod)) ⟩
        Y .ψ (F.₀ (d' .cod)) ℰ.∘ D.₁ (d' .map)            ≡⟨ Y .commutes (d' .map) ⟩
        Y .ψ d                                            ∎
      .is-iso.rinv _ → ext refl
      .is-iso.linv _ → ext refl

    Restrict-cocone-is-precat-iso : is-precat-iso (Restrict-cocone D)
    Restrict-cocone-is-precat-iso .has-is-ff = Restrict-cocone-ff
    Restrict-cocone-is-precat-iso .has-is-iso = snd $
      Cocone≃cocone _ ∙e Σ-ap-snd (λ _ → restrict-cocone≃) ∙e Cocone≃cocone _ e⁻¹

    Restrict-cocone-is-equivalence : is-equivalence (Restrict-cocone D)
    Restrict-cocone-is-equivalence = is-precat-iso→is-equivalence Restrict-cocone-is-precat-iso

    module Restrict-cocone = is-equivalence Restrict-cocone-is-equivalence
```

Since `Restrict-cocone`{.Agda} is an equivalence, it preserves initial
objects, i.e. colimiting cocones. In other words, if $K$ is a colimit
of $D$, then its restriction is a colimit of $D F$.

```agda
    restrict-is-colimit
      : ∀ {coapex}
      → (K : D => Const coapex)
      → is-colimit D coapex K
      → is-colimit (D F∘ F) coapex (restrict-cocone D K)
    restrict-is-colimit {coapex} K colim =
      generalize-colimitp
        (is-initial-cocone→is-colimit _
          (left-adjoint→initial (Restrict-cocone.F⊣F⁻¹)
            (is-colimit→is-initial-cocone _ colim)))
        refl
```

But we can also go the other way: if $K$ is a colimit of $D F$,
then its extension is a colimit of $D$.

```agda
    extend-is-colimit
      : ∀ {coapex} (K : D F∘ F => Const coapex)
      → is-colimit (D F∘ F) coapex K
      → is-colimit D coapex (extend-cocone K)
    extend-is-colimit {coapex} K colim =
      generalize-colimitp
        (is-initial-cocone→is-colimit _
          (left-adjoint→initial Restrict-cocone.F⁻¹⊣F
            (is-colimit→is-initial-cocone _ colim)))
        λ {d} → case fin.point d return
          (λ d' → extend' _ d d' ≡ extend' K d d')
        of λ d' → refl
```

Finally, we summarise these results as a [[displayed equivalence]]
between the property of being a colimit for cocones under $D$ and for
cocones under $D F$.

```agda
    final→is-colimit≃
      : ∀ {coapex}
      → is-colimit D coapex ≃[ restrict-cocone≃ ] is-colimit (D F∘ F) coapex
    final→is-colimit≃ = prop-over-ext!
      restrict-cocone≃ restrict-is-colimit extend-is-colimit
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
opaque
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
