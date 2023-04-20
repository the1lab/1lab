```agda
open import Cat.Displayed.Functor
open import Cat.Displayed.Base
open import Cat.Prelude

module Cat.Displayed.NaturalTransformation where
```

# Displayed natural transformation

Just like we have defined a [displayed functor][disfct]
$\bf{F} : \cE \to \cF$ lying over an ordinary functor $F : \cA \to \cB$
we can define a displayed natural transformation.
Assume $\bf{F}, \bf{G} : \cE \to \cF$ are [displayed functors][disfct]
over $F : \cA \to \cB$ resp. $G : \cA \to \cB$ and we have a
natural transformation $\eta : F \To G$. Than one can define a
**displayed natural transformation** $\bf{\eta} : \bf{F} \To \bf{G}$
lying over $\eta$.

[disfct]: Cat.Displayed.Functor.html

~~~{.quiver}
\[\begin{tikzcd}
	{\mathcal E} && {\mathcal F} \\
	\\
	\mathcal A && \mathcal B
	\arrow[""{name=0, anchor=center, inner sep=0}, "{\mathbf{F}}", curve={height=-12pt}, from=1-1, to=1-3]
	\arrow[""{name=1, anchor=center, inner sep=0}, "{\mathbf{G}}"', curve={height=12pt}, from=1-1, to=1-3]
	\arrow[""{name=2, anchor=center, inner sep=0}, "F", curve={height=-12pt}, from=3-1, to=3-3]
	\arrow[""{name=3, anchor=center, inner sep=0}, "G"', curve={height=12pt}, from=3-1, to=3-3]
  \arrow[category over, from=1-1, to=3-1]
	\arrow[category over, from=1-3, to=3-3]
	\arrow["\eta", shorten <=3pt, shorten >=3pt, Rightarrow, from=2, to=3]
	\arrow["{\eta^\prime}", shorten <=3pt, shorten >=3pt, Rightarrow, from=0, to=1]
\end{tikzcd}\]
~~~

```agda
module
  _ {o ℓ o′ ℓ′ o₂ ℓ₂ o₂′ ℓ₂′}
    {A : Precategory o ℓ}
    {B : Precategory o₂ ℓ₂}
    {ℰ : Displayed A o′ ℓ′}
    {ℱ : Displayed B o₂′ ℓ₂′} 
  where
  private
    lvl : Level
    lvl = o ⊔ o′ ⊔ ℓ ⊔ ℓ′ ⊔ ℓ₂′

  record _=>[_]_ {F : Functor A B} {G : Functor A B} (F′ : Displayed-functor ℰ ℱ F)
                          (η : F => G) (G′ : Displayed-functor ℰ ℱ G)
            : Type lvl where
    no-eta-equality
    private
      module ℰ = Displayed ℰ
      module ℱ = Displayed ℱ
      module η = _=>_  η
      module F′ = Displayed-functor F′
      module G′ = Displayed-functor G′    

    field
      η′ : ∀ {x} (x′ : ℰ.Ob[ x ]) → ℱ.Hom[ η.η x ] (F′.₀′ x′) (G′.₀′ x′)
      is-natural : ∀ {x y f} (x′ : ℰ.Ob[ x ]) (y′ : ℰ.Ob[ y ]) (f′ : ℰ.Hom[ f ] x′ y′)
                    → PathP
                       (λ i → ℱ.Hom[ η.is-natural x y f i ] (F′.₀′ x′) (G′.₀′ y′))
                       (η′ y′ ℱ.∘′ F′.₁′ f′) (G′.₁′ f′ ℱ.∘′ η′ x′)
```

Let $\bf{F}$ and $\bf{G}$ be fibred functors. A displayed natural transformation
$\bf{\eta} : \bf{F} \To \bf{G}$ is called **cartesian** if
$\bf{\eta}_x : \bf{F}(x) \to \bf{G}(x)$ is a vertical morphism for every $x \in \cE$,
i.e. the morphism lies over the identity. This makes only sense if $\bf{F} = \bf{G}$.
This means that the underlying natural transformation $\eta$ is the
identity natural transformation. 
```agda
  record Cartesian-natural-transformation
      {F : Functor A B} (F′ : Fibred-functor ℰ ℱ F) (G′ : Fibred-functor ℰ ℱ F)
      : Type (lvl ⊔ o₂ ⊔ ℓ₂ ⊔ o₂′) where
    no-eta-equality
    private
      module B = Precategory B
      module ℰ = Displayed ℰ
      module ℱ = Displayed ℱ
      module F = Functor F
      module F′ = Fibred-functor F′
      module G′ = Fibred-functor G′
      
    field
      η′ : ∀ {x} (x′ : ℰ.Ob[ x ]) → ℱ.Hom[ B.id ] (F′.₀′ x′) (G′.₀′ x′)
      is-natural′ : ∀ {x y f} (x′ : ℰ.Ob[ x ]) (y′ : ℰ.Ob[ y ]) (f′ : ℰ.Hom[ f ] x′ y′)
                    → PathP
                       (λ i → ℱ.Hom[ (B.idl (F.₁ f) ∙ sym (B.idr (F.₁ f))) i ]
                       (F′.₀′ x′) (G′.₀′ y′))
                       (η′ y′ ℱ.∘′ F′.₁′ f′) (G′.₁′ f′ ℱ.∘′ η′ x′)
``` 

In many cases the cartesian natural transformation is between displayed functors
between displayed categories living over the same base category.
```agda
module
  _ {o ℓ o′ ℓ′ o′′ ℓ′′}
    {B : Precategory o ℓ}
    {ℰ : Displayed B o′ ℓ′}
    {ℱ : Displayed B o′′ ℓ′′} 
  where
  private
    lvl : Level
    lvl = o ⊔ o′ ⊔ ℓ ⊔ ℓ′ ⊔ ℓ′′

  record _=>′_ (F′ G′ : Fibred-functor-single-base ℰ ℱ) : Type lvl where
    no-eta-equality
    private
      module B = Precategory B
      module ℰ = Displayed ℰ
      module ℱ = Displayed ℱ
      module F′ = Fibred-functor-single-base F′
      module G′ = Fibred-functor-single-base G′
      
    field
      η′ : ∀ {x} (x′ : ℰ.Ob[ x ]) → ℱ.Hom[ B.id ] (F′.₀′ x′) (G′.₀′ x′)
      is-natural′ : ∀ {x y f} (x′ : ℰ.Ob[ x ]) (y′ : ℰ.Ob[ y ]) (f′ : ℰ.Hom[ f ] x′ y′)
                    → PathP
                       (λ i → ℱ.Hom[ (B.idl f ∙ sym (B.idr  f)) i ]
                       (F′.₀′ x′) (G′.₀′ y′))
                       (η′ y′ ℱ.∘′ F′.₁′ f′) (G′.₁′ f′ ℱ.∘′ η′ x′)
```
