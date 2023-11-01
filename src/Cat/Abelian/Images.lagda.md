<!--
```agda
open import Cat.Diagram.Equaliser.Kernel
open import Cat.Instances.Shape.Terminal
open import Cat.Functor.FullSubcategory
open import Cat.Diagram.Initial
open import Cat.Instances.Comma
open import Cat.Instances.Slice
open import Cat.Abelian.Base
open import Cat.Prelude

open /-Obj
open /-Hom
open ↓Obj
open ↓Hom
```
-->

```agda
module Cat.Abelian.Images {o ℓ} {C : Precategory o ℓ} (A : is-abelian C) where
open is-abelian A
```

# Images in abelian categories

Let $f : A \to B$ be a morphism in an [abelian category] $\cA$, which
(by definition) admits a canonical decomposition as

$$
A \xepi{p} \coker (\ker f) \cong \ker (\coker f) \xmono{i} B\text{,}
$$

where the map $p$ is [epic], $i$ is [[monic]], and the indicated
isomorphism arises from $f$ in a canonical way, using the universal
properties of kernels and cokernels. What we show in this section is
that the arrow $\ker (\coker f) \mono B$ is an [[image factorisation]]
for $f$: It is the largest monomorphism through which $f$ factors. Since
this construction does not depend on any specificities of $f$, we
conclude that every map in an abelian category factors as a [regular
epi] followed by a [regular mono].

[abelian category]: Cat.Abelian.Base.html#pre-abelian-abelian-categories
[regular epi]: Cat.Diagram.Coequaliser.RegularEpi.html
[regular mono]: Cat.Diagram.Equaliser.RegularMono.html
[monic]: Cat.Morphism.html#monos
[epic]: Cat.Morphism.html#epis

## The image

```agda
images : ∀ {A B} (f : Hom A B) → Image f
images f = im where
  the-img : ↓Obj (const! (cut f)) Forget-full-subcat
  the-img .x = tt
  the-img .y .object = cut (Ker.kernel (Coker.coeq f))
  the-img .y .witness {c} = kernels-are-subobjects C ∅ _ (Ker.has-is-kernel _)
```

Break $f$ down as an epi $p : A \epi \ker (\coker f)$ followed by a mono
$i : \ker (\coker f) \mono B$. We can take the map $i$ as the "image"
subobject. We must provide a map filling the dotted line in

~~~{.quiver .short-05}
\[\begin{tikzcd}
  A && {\mathrm{im}(f)} \\
  & B
  \arrow["i", hook, from=1-3, to=2-2]
  \arrow["f"', from=1-1, to=2-2]
  \arrow[dotted, from=1-1, to=1-3]
\end{tikzcd}\]
~~~

but this is the epimorphism $p$ in our factorisation. More precisely,
it's the epimorphism $p$ followed by the isomorphism $f'$ in the
decomposition

$$
A \xepi{p} \coker (\ker f) \xto{f'} \ker (\coker f) \xmono{i} B\text{.}
$$

```agda
  the-img .map ./-Hom.map = decompose f .fst ∘ Coker.coeq _
  the-img .map ./-Hom.commutes = pulll (Ker.factors _) ∙ Coker.factors _
```

## Universality

Suppose that we're given another decomposition of $f$ as

$$
A \xto{q} X \mono{i'} B\times{,}
$$

and we wish to construct a map $g : i' \le i$^[this is an inequality in
the poset of subobjects of $B$, which is a map $i' \to i$ in the slice
over $B$.], hence a map $\im f \to X$ such that the triangle

~~~{.quiver .short-05}
\[\begin{tikzcd}
  {\mathrm{im}(f)} & X \\
  B
  \arrow["{i'}", hook, from=1-2, to=2-1]
  \arrow["f", from=1-1, to=1-2]
  \arrow["i"', hook, from=1-1, to=2-1]
\end{tikzcd}\]
~~~

commutes.

```agda
  im : Image f
  im .Initial.bot = the-img
  im .Initial.has⊥ other = contr factor unique where
    factor : ↓Hom (const! (cut f)) Forget-full-subcat the-img other
    factor .α = tt
    factor .β ./-Hom.map =
        Coker.universal (Ker.kernel f) {e' = other .map .map} path
      ∘ coker-ker≃ker-coker f .is-invertible.inv
```

Observe that by the universal property of $\coker (\ker f)$^[hence of
$\ker (\coker f)$, after adjusting by our old friendly isomorphism], if
we have a map $q : A \to X$ such that $0 = q\ker f$, then we can obtain
a (unique) map $\coker (\ker f) \to X$ s.t. the triangle above commutes!

```agda
      where abstract
        path : other .map .map ∘ 0m ≡ other .map .map ∘ kernel f .Kernel.kernel
        path =
          other .y .witness _ _ $ sym $
                pulll (other .map .commutes)
            ·· Ker.equal f
            ·· ∅.zero-∘r _
            ·· 0m-unique
            ·· sym (ap₂ _∘_ refl ∘-zero-r ∙ ∘-zero-r)
```

To satisfy that equation, observe that since $i'$ is monic, it suffices
to show that $i'0 = i'q\ker f$, but we have assumed that $i'q = f$, and
$f\ker f = 0$ by the definition of kernel. Some tedious
isomorphism-algebra later, we have shown that $\ker (\coker f) \mono B$
is the image of $f$.

<details>
<summary>Here's the tedious isomorphism algebra.</summary>

```agda
    factor .β ./-Hom.commutes = invertible→epic (coker-ker≃ker-coker f) _ _ $
      Coker.unique₂ (Ker.kernel f)
        (sym (Ker.equal f ∙ ∅.zero-∘r _ ∙ 0m-unique ∙ sym ∘-zero-r))
        (ap₂ _∘_ ( sym (assoc _ _ _)
                        ∙ ap₂ _∘_ refl (cancelr
                          (coker-ker≃ker-coker f .is-invertible.invr))) refl
              ∙ pullr (Coker.factors _) ∙ other .map .commutes)
        (sym (decompose f .snd ∙ assoc _ _ _))
    factor .sq = /-Hom-path $ sym $ other .y .witness _ _ $
      pulll (factor .β .commutes)
      ∙ the-img .map .commutes
      ·· sym (other .map .commutes)
      ·· ap (other .y .object .map ∘_) (intror refl)

    unique : ∀ x → factor ≡ x
    unique x = ↓Hom-path _ _ refl $ /-Hom-path $ other .y .witness _ _ $
      sym (x .β .commutes ∙ sym (factor .β .commutes))
```
</details>
