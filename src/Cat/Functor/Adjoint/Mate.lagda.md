<!--
```agda
open import Cat.Functor.Adjoint
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Reasoning
```
-->

```agda
module Cat.Functor.Adjoint.Mate where
```

# Mates

Let $F \dashv U : A \to B$, $F' \dashv U' : A' \to B'$ be a pair of
adjunctions, and let $X : A \to A'$ and $Y : B \to B'$ be a pair of
functors, fitting together into a diagram

~~~{.quiver}
\begin{tikzcd}
  A && B \\
  \\
  {A'} && {B'\text{,}}
  \arrow[""{name=0, anchor=center, inner sep=0}, "U", curve={height=-6pt}, from=1-3, to=1-1]
  \arrow[""{name=1, anchor=center, inner sep=0}, "F", curve={height=-6pt}, from=1-1, to=1-3]
  \arrow[""{name=2, anchor=center, inner sep=0}, "{F'}", curve={height=-6pt}, from=3-1, to=3-3]
  \arrow[""{name=3, anchor=center, inner sep=0}, "{U'}", curve={height=-6pt}, from=3-3, to=3-1]
  \arrow["X"', from=1-1, to=3-1]
  \arrow["Y", from=1-3, to=3-3]
  \arrow["\dashv"{anchor=center, rotate=-90}, draw=none, from=1, to=0]
  \arrow["\dashv"{anchor=center, rotate=-90}, draw=none, from=2, to=3]
\end{tikzcd}
~~~

which needn't necessarily commute. By pasting with the adjunction units
and counits, there is an equivalence between the sets of natural
transformations $XU \to U'Y$ and $F'X \to YF$, which in one direction
sends

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  B \&\& {B'} \\
  \\
  A \&\& {A'}
  \arrow["Y", from=1-1, to=1-3]
  \arrow["{U'}", from=1-3, to=3-3]
  \arrow["X"', from=3-1, to=3-3]
  \arrow["U"', from=1-1, to=3-1]
  \arrow["\alpha", Rightarrow, from=3-1, to=1-3]
\end{tikzcd}\]
~~~

to

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  \textcolor{rgb,255:red,92;green,92;blue,214}{A} \&\& \textcolor{rgb,255:red,92;green,92;blue,214}{B} \&\& \textcolor{rgb,255:red,92;green,92;blue,214}{B} \&\& \textcolor{rgb,255:red,214;green,92;blue,92}{B'} \\
  \\
  \&\& \textcolor{rgb,255:red,214;green,92;blue,92}{A} \&\& \textcolor{rgb,255:red,214;green,92;blue,92}{A'\text{.}}
  \arrow["{\Id}", from=1-5, to=1-7]
  \arrow["Y", color={rgb,255:red,92;green,92;blue,214}, from=1-3, to=1-5]
  \arrow["F", color={rgb,255:red,92;green,92;blue,214}, from=1-1, to=1-3]
  \arrow["U", from=1-3, to=3-3]
  \arrow[""{name=0, anchor=center, inner sep=0}, "{\Id}"', from=1-1, to=3-3]
  \arrow["{U'}"', from=1-5, to=3-5]
  \arrow["X"', color={rgb,255:red,214;green,92;blue,92}, from=3-3, to=3-5]
  \arrow[""{name=1, anchor=center, inner sep=0}, "{F'}"', color={rgb,255:red,214;green,92;blue,92}, from=3-5, to=1-7]
  \arrow["\alpha", Rightarrow, from=3-3, to=1-5]
  \arrow["\eta", shorten <=6pt, Rightarrow, from=0, to=1-3]
  \arrow["\epsilon"', shorten >=6pt, Rightarrow, from=1-5, to=1]
\end{tikzcd}\]
~~~

We call natural transformations $\alpha : XU \to U'Y$ and $\beta : F'X
\to YF$ **mates**, with respect to the adjunctions $F \dashv U$ and $F'
\dashv U'$, if they correspond under this equivalence.

<!--
```agda
open Functor

module _
  {oa ℓa ob ℓb oc ℓc od ℓd}
  {A : Precategory oa ℓa}
  {A' : Precategory ob ℓb}
  {B : Precategory oc ℓc}
  {B' : Precategory od ℓd}
  {F : Functor A B}
  {U : Functor B A}
  {F' : Functor A' B'}
  {U' : Functor B' A'}
  (F⊣U : F ⊣ U)
  (F'⊣U' : F' ⊣ U')
  (X : Functor A A')
  (Y : Functor B B')
  where
  private
    module F⊣U = _⊣_ F⊣U
    module F'⊣U' = _⊣_ F'⊣U'
    module U = Cat.Functor.Reasoning U
    module U' = Cat.Functor.Reasoning U'
    module F = Cat.Functor.Reasoning F
    module F' = Cat.Functor.Reasoning F'
    module X = Cat.Functor.Reasoning X
    module Y = Cat.Functor.Reasoning Y
    module A = Cat.Reasoning A
    module B = Cat.Reasoning B
    module A' = Cat.Reasoning A'
    module B' = Cat.Reasoning B'

  private
    η : ∀ {x} → A.Hom x (U.₀ (F.₀ x))
    η = F⊣U.unit.η _

    ε : ∀ {x} → B.Hom (F.₀ (U.₀ x)) x
    ε = F⊣U.counit.ε _

    η' : ∀ {x} → A'.Hom x (U'.₀ (F'.₀ x))
    η' = F'⊣U'.unit.η _

    ε' : ∀ {x} → B'.Hom (F'.₀ (U'.₀ x)) x
    ε' = F'⊣U'.counit.ε _
```
-->

Unfortunately, proof assistants: if we were to define mates by pasting,
we would get a natural transformation with much worse _definitional_
behaviour. Therefore, we calculate the mate of a transformation $\alpha
: XU \to U'Y$ by hand.

```agda
  mate : (X F∘ U) => (U' F∘ Y) → (F' F∘ X) => (Y F∘ F)
  mate α = nt module mate where
    module α = _=>_ α

    nt : (F' F∘ X) => (Y F∘ F)
    nt ._=>_.η _ =
      ε' B'.∘ F'.₁ (α.η _) B'.∘ F'.₁ (X.₁ η)
    nt ._=>_.is-natural x y f =
      (ε' B'.∘ F'.₁ (α.η _) B'.∘ F'.₁ (X.₁ η)) B'.∘ F'.₁ (X.₁ f)              ≡⟨ B'.extendr (B'.pullr (F'.weave (X.weave (F⊣U.unit.is-natural _ _ _)))) ⟩
      (ε' B'.∘ F'.₁ (α.η _)) B'.∘ F'.₁ (X.₁ (U.₁ (F.₁ f))) B'.∘ F'.₁ (X.₁ η)  ≡⟨ B'.extendl (B'.extendr (F'.weave (α.is-natural _ _ _))) ⟩
      (ε' B'.∘ F'.₁ (U'.₁ (Y.₁ (F.₁ f)))) B'.∘ F'.₁ (α.η _) B'.∘ F'.₁ (X.₁ η) ≡⟨ B'.pushl (F'⊣U'.counit.is-natural _ _ _) ⟩
      Y.₁ (F.₁ f) B'.∘ (ε' B'.∘ F'.₁ (α.η _) B'.∘ F'.₁ (X.₁ η))               ∎
```

By a very similar calculation, we can define the mate of $\beta : F'X
\to YF$.

```agda
  mate-inv : (F' F∘ X) => (Y F∘ F) → (X F∘ U) => (U' F∘ Y)
  mate-inv α = nt module mate-inv where
    module α = _=>_ α

    nt : (X F∘ U) => (U' F∘ Y)
    nt ._=>_.η _ =
      U'.₁ (Y.₁ ε) A'.∘ U'.₁ (α.η _) A'.∘ η'
    nt ._=>_.is-natural x y f =
      (U'.₁ (Y.₁ ε) A'.∘ U'.₁ (α.η _) A'.∘ η') A'.∘ X.₁ (U.₁ f)                     ≡⟨ A'.extendr (A'.pullr (F'⊣U'.unit.is-natural _ _ _)) ⟩
      (U'.₁ (Y.₁ ε) A'.∘ U'.₁ (α.η (U.₀ y))) A'.∘ U'.₁ (F'.₁ (X.₁ (U.₁ f))) A'.∘ η' ≡⟨ A'.extendl (A'.extendr (U'.weave (α.is-natural _ _ _))) ⟩
      (U'.₁ (Y.₁ ε) A'.∘ U'.₁ (Y.₁ (F.₁ (U.₁ f)))) A'.∘ U'.₁ (α.η _) A'.∘ η'        ≡⟨ A'.pushl (U'.weave (Y.weave (F⊣U.counit.is-natural _ _ f))) ⟩
      U'.₁ (Y.₁ f) A'.∘ U'.₁ (Y.₁ ε) A'.∘ U'.₁ (α.η _) A'.∘ η'                      ∎
```

By some rather tedious applications of the triangle identities, we can
calculate that the operations `mate`{.Agda} and `mate-inv`{.Agda} are
inverse equivalences.

```agda
  mate-invl : ∀ (α : (F' F∘ X) => (Y F∘ F)) → mate (mate-inv α) ≡ α
  mate-invl α =
    Nat-path λ _ →
    ε' B'.∘ ⌜ F'.₁ (U'.₁ (Y.₁ ε) A'.∘ U'.₁ (α.η _) A'.∘ η') ⌝ B'.∘ F'.₁ (X.₁ η)           ≡⟨ ap! (F'.F-∘ _ _ ∙ (ap₂ B'._∘_ refl (F'.F-∘ _ _))) ⟩
    ε' B'.∘ (F'.₁ (U'.₁ (Y.₁ ε)) B'.∘ F'.₁ (U'.₁ (α.η _)) B'.∘ F'.₁ η') B'.∘ F'.₁ (X.₁ η) ≡⟨ B'.extendl (B'.pulll (F'⊣U'.counit.is-natural _ _ _)) ⟩
    (Y.₁ ε B'.∘ ε') B'.∘ (F'.₁ (U'.₁ (α.η _)) B'.∘ F'.₁ η') B'.∘ F'.₁ (X.₁ η)             ≡⟨ B'.extendl (B'.pulll (B'.pullr (F'⊣U'.counit.is-natural _ _ _))) ⟩
    (Y.₁ ε B'.∘ α.η _ B'.∘ ε') B'.∘ F'.₁ η' B'.∘ F'.₁ (X.₁ η)                             ≡⟨ B'.pulll (B'.pullr (B'.cancelr F'⊣U'.zig)) ⟩
    (Y.₁ ε B'.∘ α.η _) B'.∘ F'.₁ (X.₁ η)                                                  ≡⟨ B'.pullr (α.is-natural _ _ _) ⟩
    Y.₁ ε B'.∘ Y.₁ (F.₁ η) B'.∘ α.η _                                                     ≡⟨ B'.cancell (Y.annihilate F⊣U.zig) ⟩
    α.η _                                                                                 ∎
    where module α = _=>_ α

  mate-invr : ∀ (α : (X F∘ U) => (U' F∘ Y)) → mate-inv (mate α) ≡ α
  mate-invr α =
    Nat-path λ _ →
    U'.₁ (Y.₁ ε) A'.∘ ⌜ U'.₁ (ε' B'.∘ F'.₁ (α.η _) B'.∘ F'.₁ (X.₁ η)) ⌝ A'.∘ η'           ≡⟨ ap! (U'.F-∘ _ _ ∙ (ap₂ A'._∘_ refl (U'.F-∘ _ _))) ⟩
    U'.₁ (Y.₁ ε) A'.∘ (U'.₁ ε' A'.∘ U'.₁ (F'.₁ (α.η _)) A'.∘ U'.₁ (F'.₁ (X.₁ η))) A'.∘ η' ≡⟨ ap₂ A'._∘_ refl (A'.extendr (A'.pullr (sym (F'⊣U'.unit.is-natural _ _ _)))) ⟩
    U'.₁ (Y.₁ ε) A'.∘ (U'.₁ ε' A'.∘ U'.₁ (F'.₁ (α.η _))) A'.∘ η' A'.∘ X.₁ η               ≡⟨ ap₂ A'._∘_ refl (A'.pullr (A'.extendl (sym (F'⊣U'.unit.is-natural _ _ _)))) ⟩
    U'.₁ (Y.₁ ε) A'.∘ U'.₁ ε' A'.∘ η' A'.∘ α.η _ A'.∘ X.₁ η                               ≡⟨ ap₂ A'._∘_ refl (A'.cancell F'⊣U'.zag) ⟩
    U'.₁ (Y.₁ ε) A'.∘ α.η _ A'.∘ X.₁ η                                                    ≡⟨ A'.pulll (sym (α.is-natural _ _ _)) ⟩
    (α.η _ A'.∘ X.₁ (U.₁ ε)) A'.∘ X.₁ η                                                   ≡⟨ A'.cancelr (X.annihilate F⊣U.zag) ⟩
    α.η _                                                                                 ∎
    where module α = _=>_ α

  mate-is-equiv : is-equiv mate
  mate-is-equiv = is-iso→is-equiv (iso mate-inv mate-invl mate-invr)
```
