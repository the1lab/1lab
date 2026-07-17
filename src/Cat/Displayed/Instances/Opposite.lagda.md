<!--
```agda
open import Cat.Displayed.Cartesian
open import Cat.Functor.Naturality
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Cartesian.Indexing as Ix
import Cat.Displayed.Fibre.Reasoning as Fib
import Cat.Displayed.Reasoning as Disp
import Cat.Functor.Reasoning as Fr
import Cat.Reasoning as Cat
```
-->

```agda
module Cat.Displayed.Instances.Opposite
  {o ℓ o' ℓ'} {B : Precategory o ℓ} (E : Displayed B o' ℓ')
  (cart : Cartesian-fibration E)
  where
```

# The opposite of a fibration

<!--
```agda
open Cartesian-fibration E cart
open Ix E cart
open Cat B
open _=>_

private
  module rebase {x} {y} {f : Hom x y} = Fr (base-change f)
  module D = Displayed
  open module E = Disp E
  module F = Fib E
  open F renaming (_∘_ to infixr 25 _∘v_) using ()

  γ← = ^*-comp-from
  γ→ = ^*-comp-to
  ι← = ^*-id-from
  ι→ = ^*-id-to
  _[_] = rebase
  infix 45 _[_]
```
-->

::: source
The construction formalised here, defined in terms of an *operation*
which assigns [[Cartesian lifts]], is due to Sterling [-@relativect];
there it is introduced as a simplification of a construction to Bénabou
as relayed by Streicher [-@Streicher:fibred-cats]. In the univalent
setting, the extra generality afforded by Bénabou's construction would
only be relevant in the setting of uncloven fibrations *of
precategories*; we have thus decided to avoid its complexity.
:::

Since the theory of [[fibrations]] over $\cB$ behaves like ordinary
category theory over $\Sets$, we expect to find $\cB$-indexed analogues
of basic constructions such as functor categories, product categories,
and, what concerns us here, *opposite* categories. Working at the level
of [[displayed categories]], fix a fibration $\cE \liesover \cB$; we
want to construct the fibration which classifies[^catcore]

$$
\cB\op \xto{\cE^*(-)} \Cat \xto{(-)\op} \Cat
$$,

[^catcore]:
    Note that, strictly speaking, the construction of opposite
    categories can not be extended to a pseudofunctor $\Cat \to \Cat$:
    While the opposite of a functor goes in the same direction as the
    original (i.e.  $F : \cC \to \cD$ is taken to $F\op : \cC\op \to
    \cD\op$), the opposite of a *natural transformation* has reversed
    direction --- the dual of $\eta : F \to G$ is $\eta\op : G\op \to
    F\op$. To capture this, the "opposite category functor" would need
    to be typed $\Cat \to \Cat^{\rm{co}}$ instead, indicating that it
    reverses 2-cells.

    However, because the domain $\cB\op$ is [[locally discrete|locally
    discrete bicategory]], all of its 2-cells are isomorphisms.
    Therefore, the pseudofunctor classified by a given fibration factors
    through the *homwise [[core]]* of $\Cat$ --- and the construction of
    opposite categories restricts to a map $\Cat^{\rm{core}} \to
    \Cat^{\rm{core}}$.

in other words, the fibration whose [[fibre categories]] are the
opposites of those of $\cE$. Note that this is still a category over
$\cB$, unlike in the case of the [[total opposite]], which results in a
category over $\cB\op$ --- which, generally, will not be a fibration.
The construction of the fibred opposite proceeds using $\cE$'s
[[base change]] functors. A morphism $h : x \to\op_f y$, lying over a map
$f : a \to b$, is defined to be a map $f^*y \to_{\id} x$, as indicated
(in red) in the diagram below.

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  x \&\& {f^*y} \&\& y \\
  \\
  a \&\& a \&\& b
  \arrow["\pi", from=1-3, to=1-5]
  \arrow[lies over, from=1-5, to=3-5]
  \arrow[lies over, from=1-3, to=3-3]
  \arrow["f"', from=3-3, to=3-5]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-3, to=3-5]
	\arrow["h"', color={rgb,255:red,214;green,92;blue,92}, from=1-3, to=1-1]
  \arrow[Rightarrow, no head, from=3-1, to=3-3]
  \arrow[lies over, from=1-1, to=3-1]
\end{tikzcd}\]
~~~

At the level of vertical maps, this says that a morphism $x \to\op y$ is
determined by a morphism $\id^*y \to x$, hence by a morphism $y \to x$;
this correspondence trivially extends to an [[isomorphism of
precategories]] between $\cE^*(x)\op$ and $\cE^*_{\rm{op}}(x)$. If we
have maps $h : f^*z \to y$ and $h': g^*y \to x$, we can obtain a map
$fg^*z \to x$ to stand for their opposite in $\cE\op$ by calculating

$$
fg^*z \xto{\gamma} g^*f^*z \xto{f^*h} g^*y \xto{h'} x
$$,

where the map $\gamma$ is one of the structural morphisms expressing
[[pseudofunctoriality|pseudofunctor]] of $\cE^*(-)$.

```agda
_∘,_
  : ∀ {a b c} {x y z} {f : Hom b c} {g : Hom a b}
  → (f' : Hom[ id ] (f ^* z) y) (g' : Hom[ id ] (g ^* y) x)
  → Hom[ id {x = a} ] ((f ∘ g) ^* z) x
_∘,_ {g = g} f' g' = g' ∘v g [ f' ] ∘v γ→
```

## The coherence problem

Having done the mathematics behind the fibred opposite, we turn to
teaching Mikan the construction. Recall that the algebraic laws
(associativity, unitality) of a displayed category $\cE \liesover \cB$
are *dependent paths* over the corresponding laws in $\cB$. Ordinarily,
this dependence is strictly at the level of morphisms depending on
morphisms, with the domain and codomain staying fixed --- and we have an
extensive toolkit of combinators for dealing with this indexing.

However, the fibred opposite mixes levels in a complicated way. For
concreteness, let's focus on the right identity law. We want to
construct a path between some $h : f^*y \to x$ and the composite

$$
(f\id)^*y \xto{\gamma} {\id}^*f^*y \xto{{\id}^*h} {\id}^*x \xto{\pi} x
$$,

but note that, while these are both vertical maps, they have different
*domains*! While the path we're trying to construct *is* allowed to
depend on the witness that $f\id = f$ in $\cB$, introducing this
dependency on the domain *object* actually complicates things even
further. Our toolkit does not include very many tools for working with
dependent identifications between maps whose source and target vary.

The solution is to reify the dependency of the identifications into a
*morphism*, which we can then calculate with at the level of fibre
categories. Given a path $p : f = f'$, we obtain a vertical map $f'^*x
\to f^*x$, which we call the `adjust`{.Agda}ment induced by $p$. The
explicit definition below is identical to transporting the identity map
$f^*x \to f^*x$ along $p$, but computes better:

```agda
private
  adjust
    : ∀ {a b} {f f' : Hom a b} {x : Ob[ b ]}
    → (p : f ≡ f')
    → Hom[ id ] (f' ^* x) (f ^* x)
  adjust p = π*.universal' (idr _ ∙ p) (π* _ _)
```

<!--
```agda
  π : ∀ {x y} {f : Hom x y} {y' : Ob[ y ]} → Hom[ f ] (f ^* y') y'
  π = π* _ _

private abstract
  π-adjust
    : ∀ {a b} {f f' : Hom a b} {x : Ob[ b ]} (p : f ≡ f')
    → π* f x ∘' adjust p ≡[ refl ∙ idr f ∙ p ] π* f' x
  π-adjust p = π*.commutes _ _ ∙[] to-pathp[]⁻ refl

  adjust-refl
    : ∀ {a b} {f : Hom a b} {x : Ob[ b ]}
    → adjust {x = x} (λ i → f) ≡ id'
  adjust-refl = π*.uniquep₂ (idr _) refl (idr _) (adjust refl) id'
    (to-pathp[] (ap E.hom[] (π*.commutes _ _) ∙∙ E.hom[]-∙ _ _ ∙∙ E.liberate _))
    (idr' _)
```
-->

The point of introducing `adjust`{.Agda} is the following theorem, which
connects transport in the domain of a vertical morphism with
postcomposition along `adjust`{.Agda}. The proof is by path induction:
it suffices to cover the case where the domain varies trivially, which
leads to a correspondingly trivial adjustment.

```agda
  transp-lift
    : ∀ {a b} {f f' : Hom a b} {x : Ob[ b ]} {y : Ob[ a ]} {h : Hom[ id ] (f ^* x) y}
    → (p : f ≡ f')
    → transport (λ i → Hom[ id ] (p i ^* x) y) h ≡ h ∘v adjust p
  transp-lift {f = f} {x = x} {y} {h} =
    J (λ f' p → transport (λ i → Hom[ id ] (p i ^* x) y) h ≡ E.hom[ idl id ] (h ∘' adjust p))
      ( transport-refl _
      ∙ sym (ap E.hom[] (ap₂ _∘'_ refl adjust-refl)
      ∙ ap E.hom[] (from-pathp[]⁻ (idr' h)) ∙ E.hom[]-∙ _ _ ∙ E.liberate _))
```

To finish, we'll need to connect the `adjust`{.Agda}ment induced by the
algebraic laws of $\cB$ with the pseudofunctoriality witnesses of $\cE$.

```agda
  adjust-idr
    : ∀ {a b} {f : Hom a b} {x : Ob[ b ]}
    → adjust {x = x} (idr f) ≡ γ← ∘v ι←

  adjust-idl
    : ∀ {a b} {f : Hom a b} {x : Ob[ b ]}
    → adjust {x = x} (idl f) ≡ γ← ∘v f [ ι← ]

  adjust-assoc
    : ∀ {a b c d} {f : Hom c d} {g : Hom b c} {h : Hom a b} {x : Ob[ d ]}
    → adjust {x = x} (assoc f g h) ≡ γ← ∘v γ← ∘v h [ γ→ ] ∘v γ→
```

<details>
<summary>The proofs here are nothing more than calculations at the level
of the underlying displayed category. They're not informative; it's fine
to take the three theorems above as given.</summary>

```agda
  adjust-idr {f = f} {x} = π*.uniquep₂ _ _ _ _ _ (π-adjust (idr f)) $ begin
    π ∘' (γ← ∘v ι←) ≡[]⟨ F.pulllf (π*.commutesv (π ∘' π)) ⟩
    (π ∘' π) ∘' ι←  ≡[]⟨ E.pullr[] (idr id) (π*.commutesp (idr id) id') ⟩
    π ∘' id'        ≡[]⟨ idr' π ⟩
    π               ∎[]

  adjust-idl {f = f} {x} = π*.uniquep₂ _ _ _ _ _ (π-adjust (idl f)) $ begin
    π ∘' (γ← ∘v f [ ι← ]) ≡[]⟨ F.pulllf (π*.commutesv (π ∘' π)) ⟩
    (π ∘' π) ∘' f [ ι← ]  ≡[]⟨ E.pullr[] _ (π*.commutesp id-comm (ι← ∘' π)) ⟩
    π ∘' ι← ∘' π          ≡[]⟨ E.pulll[] _ (π*.commutesp (idr id) id') ⟩
    id' ∘' π              ≡[]⟨ idl' _ ⟩
    π                     ∎[]

  adjust-assoc {f = f} {g} {h} = π*.uniquep₂ _ _ _ _ _ (π-adjust (assoc f g h)) $ begin
    π ∘' (γ← ∘v γ← ∘v h [ γ→ ] ∘v γ→)    ≡[]⟨ F.pulllf (π*.commutesv _) ⟩
    (π ∘' π) ∘' (γ← ∘v h [ γ→ ] ∘v γ→)   ≡[]⟨ pullr[] _ (F.pulllf (π*.commutesp (idr (g ∘ h)) _)) ⟩
    π ∘' (π ∘' π) ∘' (h [ γ→ ] ∘v γ→ )   ≡[]⟨ refl⟩∘'⟨ pullr[] (id-comm ∙ sym (idr (id ∘ h))) (F.pulllf (π*.commutesp _ _)) ⟩
    π ∘' π ∘' (γ→ ∘' π) ∘' γ→            ≡[]⟨ refl⟩∘'⟨ pulll[] _ (pulll[] (idr g) (π*.commutesp _ _)) ⟩
    π ∘' (π*.universal _ (π) ∘' π) ∘' γ→ ≡[]⟨ pulll[] _ (pulll[] _ (π*.commutes _ _)) ⟩
    (π ∘' π) ∘' γ→                       ≡[]⟨ pullr[] (idr h) (π*.commutesp _ _) ⟩
    π ∘' π*.universal _ _                ≡[]⟨ π*.commutes _ _ ⟩
    π                                    ∎[]
```

</details>

## The construction

Using `adjust`{.Agda}, and the three theorems above, we can tackle each
of the three laws in turn. Having boiled the proofs down to reasoning
about coherence morphisms in a pseudofunctor, the proofs are... no more
than reasoning about coherence morphisms in a pseudofunctor --- which is
to say, boring algebra. Let us make concrete note of the *data* of the
fibrewise opposite before tackling the properties:

```agda
_^op' : Displayed B o' ℓ'
_^op' .D.Ob[_] = Ob[_]
_^op' .D.Hom[_]     f x y = Hom[ id ] (f ^* y) x
_^op' .D.Hom[_]-set f x y = Hom[_]-set _ _ _
_^op' .D.id'  = π
_^op' .D._∘'_ = _∘,_
```

We can look at the case of left identity as a representative example.
Note that, after applying the generic `transp-lift`{.Agda} and the
specific lemma --- in this case, `adjust-idl`{.Agda} --- we're reasoning
entirely in the fibres of $\cE$. This lets us side-step most of the
indexed nonsense that otherwise haunts working with fibrations.

```agda
_^op' .D.idl' {x = x} {y} {f = f} f' = to-pathp $
  transport (λ i → Hom[ id ] (idl f i ^* y) x) _  ≡⟨ transp-lift _ ∙ ap₂ _∘v_ refl adjust-idl ⟩
  (f' ∘v f [ π ] ∘v γ→) ∘v γ← ∘v f [ ι← ]         ≡⟨ F.pullr (F.pullr refl) ⟩
  f' ∘v f [ π ] ∘v γ→ ∘v (γ← ∘v f [ ι← ])         ≡⟨ ap₂ _∘v_ refl (ap₂ _∘v_ refl (F.cancell (^*-comp .F.invl))) ⟩
  f' ∘v f [ π ] ∘v f [ ι← ]                       ≡⟨ F.elimr (rebase.annihilate (E.cancel _ _ (π*.commutesv _))) ⟩
  f'                                              ∎
```

The next two cases are very similar, so we'll present them without
further comment.

```agda
_^op' .D.idr' {x = x} {y} {f} f' = to-pathp $
  transport (λ i → Hom[ id ] (idr f i ^* y) x) _ ≡⟨ transp-lift _ ∙ ap₂ _∘v_ refl adjust-idr ⟩
  (π ∘v id [ f' ] ∘v γ→) ∘v γ← ∘v ι←             ≡⟨ F.pullr (F.pullr (F.cancell (^*-comp .F.invl))) ⟩
  π ∘v id [ f' ] ∘v ι←                           ≡⟨ ap (π ∘v_) (sym (base-change-id .Isoⁿ.from .is-natural _ _ _)) ⟩
  π ∘v ι← ∘v f'                                  ≡⟨ F.cancell (base-change-id .Isoⁿ.invl ηₚ _) ⟩
  f'                                             ∎

_^op' .D.assoc' {x = x} {y} {z} {f} {g} {h} f' g' h' = to-pathp $
  transport (λ i → Hom[ id ] (assoc f g h i ^* _) _) (f' ∘, (g' ∘, h'))          ≡⟨ transp-lift _ ∙ ap₂ _∘v_ refl adjust-assoc ⟩
  ((h' ∘v h [ g' ] ∘v γ→) ∘v (g ∘ h) [ f' ] ∘v γ→) ∘v γ← ∘v γ← ∘v h [ γ→ ] ∘v γ→ ≡⟨ sym (F.assoc _ _ _) ∙ F.pullr (F.pullr (ap (γ→ ∘v_) (F.pullr refl))) ⟩
  h' ∘v h [ g' ] ∘v γ→ ∘v (g ∘ h) [ f' ] ∘v ⌜ γ→ ∘v γ← ∘v γ← ∘v h [ γ→ ] ∘v γ→ ⌝ ≡⟨ ap (λ e → h' ∘v h [ g' ] ∘v γ→ ∘v (g ∘ h) [ f' ] ∘v e) (F.cancell (^*-comp .F.invl))  ⟩
  h' ∘v h [ g' ] ∘v ⌜ γ→ ∘v (g ∘ h) [ f' ] ∘v γ← ∘v h [ γ→ ] ∘v γ→ ⌝             ≡⟨ ap (λ e → h' ∘v h [ g' ] ∘v e) (F.extendl (sym (^*-comp-to-natural _))) ⟩
  h' ∘v h [ g' ] ∘v h [ g [ f' ] ] ∘v γ→ ∘v γ← ∘v h [ γ→ ] ∘v γ→                 ≡⟨ ap₂ _∘v_ refl (F.pulll (sym (rebase.F-∘ _ _)) ∙ ap₂ _∘v_ refl (F.cancell (^*-comp .F.invl))) ⟩
  h' ∘v h [ g' ∘v g [ f' ] ] ∘v h [ γ→ ] ∘v γ→                                   ≡⟨ ap (h' ∘v_) (rebase.pulll (F.pullr refl)) ⟩
  h' ∘v h [ g' ∘v g [ f' ] ∘v γ→ ] ∘v γ→                                         ∎
```

<!--
```agda
_^op' .D.hom[_] p f' = hom[ idl id ] (f' ∘' adjust p)
_^op' .D.coh[_] p f' = to-pathp (transp-lift _)
```
-->

Having defined the fibration, we can prove the comparison theorem
mentioned in the introductory paragraph, showing that passing from $\cE$
to $\cE\op$ inverts *each fibre*.

```agda
opposite-map : ∀ {a} {x y : Ob[ a ]} → Fib.Hom E y x ≃ Fib.Hom _^op' x y
opposite-map .fst f = f ∘v π
opposite-map .snd = is-iso→is-equiv $ iso
  (λ f → f ∘v π*.universalv id')
  (λ x → F.cancelr (base-change-id .Isoⁿ.invr ηₚ _))
  (λ x → F.cancelr (base-change-id .Isoⁿ.invl ηₚ _))
```

## Cartesian lifts

<!--
```agda
abstract
  ∘,-idl
    : ∀ {a b c} {x y} {f : Hom b c} {g : Hom a b} (f' : Hom[ id ] (g ^* (f ^* x)) y)
    → id' ∘, f' ≡ f' ∘v γ→
  ∘,-idl {f = f} {g} f' =
    f' ∘v g [ id' ] ∘v γ→ ≡⟨ ap (f' ∘v_) (F.eliml (base-change g .Functor.F-id)) ⟩
    f' ∘v γ→              ∎
```
-->

Since we defined the displayed morphism spaces directly in terms of
$\cE$'s base change, it's not surprising that $\cE_{\rm{op}}$ is itself
a [[fibration]]. Indeed, if we have $f : a \to b$ and $y \liesover b$, a
Cartesian lift of $y$ along $f$, *in the opposite*, boils down to asking
for something to fit into the question mark in the diagram

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  {f^*y} \&\& {f^*y} \&\& y \\
  \\
  a \&\& a \&\& {b\text{.}}
  \arrow["\pi", from=1-3, to=1-5]
  \arrow[from=1-5, to=3-5]
  \arrow[from=1-3, to=3-3]
  \arrow["f"', from=3-3, to=3-5]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-3, to=3-5]
  \arrow["?"', color={rgb,255:red,214;green,92;blue,92}, from=1-3, to=1-1]
  \arrow[Rightarrow, no head, from=3-1, to=3-3]
  \arrow[from=1-1, to=3-1]
  \arrow["\lrcorner"{anchor=center, pos=0.125, rotate=-90}, draw=none, from=1-3, to=3-1]
\end{tikzcd}\]
~~~

It's no coincidence that the boundary of the question mark is precisely
that of the identity morphism. A mercifully short calculation
establishes that this choice *does* furnish a Cartesian lift.

```agda
Opposite-cartesian : Cartesian-fibration _^op'
Opposite-cartesian f y' = record
  { lifting   = id'
  ; cartesian = record
    { universal = λ m h → h ∘v γ←
    ; commutes  = λ m h → ∘,-idl (h ∘v γ←) ∙ F.cancelr (^*-comp .F.invr)
    ; unique    = λ m h → ap (_∘v γ←) (sym h ∙ ∘,-idl m) ∙ F.cancelr (^*-comp .F.invl)
    }
  }
```
