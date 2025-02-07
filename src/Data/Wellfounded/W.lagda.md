<!--
```agda
open import 1Lab.Prelude

open import Data.Wellfounded.Properties
open import Data.Wellfounded.Base
```
-->

```agda
module Data.Wellfounded.W where
```

# W-types {defines="w-type"}

The idea behind $W$ types is much simpler than they might appear at
first brush, especially because their form is like that one of the "big
two" $\Pi$ and $\Sigma$. However, the humble $W$ is much simpler: A
value of $W_A B$ is a tree with nodes labelled by $x : A$, and such that
the branching factor of such a node is given by $B(x)$. $W$-types can be
defined inductively:

```agda
data W {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') : Type (ℓ ⊔ ℓ') where
  sup : (x : A) (f : B x → W A B) → W A B
```

<!--
```agda
W-elim : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {C : W A B → Type ℓ''}
       → ({a : A} {f : B a → W A B} → (∀ ba → C (f ba)) → C (sup a f))
       → (w : W A B) → C w
W-elim {C = C} ps (sup a f) = ps (λ ba → W-elim {C = C} ps (f ba))
```
-->

The constructor `sup`{.Agda} stands for **supremum**: it bunches up
(takes the supremum of) a bunch of subtrees, each subtree being given by
a value $y : B(x)$ of the branching factor for that node. The natural
question to ask, then, is: "supremum in _what_ order?". The order given
by the "is a subtree of" relation!

```agda
module _ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} where
  _<_ : W A B → W A B → Type _
  x < sup i f = ∃[ j ∈ B i ] (f j ≡ x)
```

This order is actually well-founded: if we want to prove a property of
$x : W_A B$, we may as well assume it's been proven for any (transitive)
subtree of $x$.

```agda
  W-well-founded : Wf _<_
  W-well-founded (sup x f) = acc λ y y<sup →
    ∥-∥-rec (Acc-is-prop _)
      (λ { (j , p) → subst (Acc _<_) p (W-well-founded (f j)) })
      y<sup
```

## Inductive types are initial algebras

<!--
```agda
module induction→initial {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') where
```
-->

We can use $W$ types to illustrate the general fact that inductive types
correspond to *initial algebras* for certain endofunctors. Here, we are
working in the "ambient" $\io$-category of types and functions, and we
are interested in the [[polynomial functor]] `P`{.Agda}:


```agda
  P : Type (ℓ ⊔ ℓ') → Type (ℓ ⊔ ℓ')
  P C = Σ A λ a → B a → C

  P₁ : {C D : Type (ℓ ⊔ ℓ')} → (C → D) → P C → P D
  P₁ f (a , h) = a , f ∘ h
```

A $P$-**algebra** (or $W$-**algebra**) is simply a type $C$ with a
function $P\,C \to C$.

```agda
  WAlg : Type _
  WAlg = Σ (Type (ℓ ⊔ ℓ')) λ C → P C → C
```

Algebras form a [[category]], where an **algebra homomorphism** is a
function that respects the algebra structure.

```agda
  _W→_ : WAlg → WAlg → Type _
  (C , c) W→ (D , d) = Σ (C → D) λ f → f ∘ c ≡ d ∘ P₁ f
```

<!--
```agda
  idW : ∀ {A} → A W→ A
  idW .fst = id
  idW .snd = refl

  _W∘_ : ∀ {A B C} → B W→ C → A W→ B → A W→ C
  (f W∘ g) .fst x = f .fst (g .fst x)
  (f W∘ g) .snd = ext λ a b → ap (f .fst) (happly (g .snd) (a , b)) ∙ happly (f .snd) _
```
-->

Now the inductive `W`{.Agda} type defined above gives us a canonical
$W$-algebra:

```agda
  W-algebra : WAlg
  W-algebra .fst = W A B
  W-algebra .snd (a , f) = sup a f
```

The claim is that this algebra is special in that it satisfies a
*universal property*: it is [[initial]] in the aforementioned category of
$W$-algebras. This means that, for any other $W$-algebra $C$, there is
exactly one homomorphism $I \to C$.

```agda
  is-initial-WAlg : WAlg → Type _
  is-initial-WAlg I = (C : WAlg) → is-contr (I W→ C)
```

Existence is easy: the algebra $C$ gives us exactly the data we need to specify a function `W A B → C`
by recursion, and the computation rules ensure that this respects the algebra structure definitionally.

```agda
  W-initial : is-initial-WAlg W-algebra
  W-initial (C , c) .centre = W-elim (λ {a} f → c (a , f)) , refl
```

For uniqueness, we proceed by induction, using the fact that `g` is a homomorphism.

```agda
  W-initial (C , c) .paths (g , hom) = Σ-pathp unique coherent where
    unique : W-elim (λ {a} f → c (a , f)) ≡ g
    unique = funext (W-elim λ {a} {f} rec → ap (λ x → c (a , x)) (funext rec)
                                          ∙ sym (hom $ₚ (a , f)))
```

There is one subtlety: being an algebra homomorphism is *not* a [proposition] in general,
so we must also show that `unique`{.Agda} is in fact an **algebra 2-cell**, i.e. that it
makes the following two identity proofs equal:

[proposition]: 1Lab.HLevel.html#is-prop

~~~{.quiver}
\[\begin{tikzcd}
	{P\,W} && {P\,C} & {P\,W} && {P\,C} \\
	\\
	W && C & W && C
	\arrow["{\text{sup}}"', from=1-1, to=3-1]
	\arrow["c", from=1-3, to=3-3]
	\arrow[""{name=0, anchor=center, inner sep=0}, "f"', curve={height=12pt}, from=3-1, to=3-3]
	\arrow[""{name=1, anchor=center, inner sep=0}, "{P\,f}"', curve={height=12pt}, from=1-1, to=1-3]
	\arrow[""{name=2, anchor=center, inner sep=0}, "{P\,g}", curve={height=-12pt}, from=1-1, to=1-3]
	\arrow["{\text{sup}}"', from=1-4, to=3-4]
	\arrow["c", from=1-6, to=3-6]
	\arrow[""{name=3, anchor=center, inner sep=0}, "f"', curve={height=12pt}, from=3-4, to=3-6]
	\arrow[""{name=4, anchor=center, inner sep=0}, "g", curve={height=-12pt}, from=3-4, to=3-6]
	\arrow[""{name=5, anchor=center, inner sep=0}, "{P\,g}", curve={height=-12pt}, from=1-4, to=1-6]
	\arrow["{P\,\text{unique}}"{description}, draw=none, from=1, to=2]
	\arrow["{\text{refl}}"{description}, draw=none, from=0, to=1]
	\arrow["{\text{unique}}"{description}, draw=none, from=3, to=4]
	\arrow["{\text{hom}}"{description}, draw=none, from=4, to=5]
\end{tikzcd}\]
~~~

Luckily, this is completely straightforward.

```agda
    coherent : Square (λ i → unique i ∘ W-algebra .snd) refl hom (λ i → c ∘ P₁ (unique i))
    coherent = transpose (flip₁ (∙-filler _ _))
```

## Initial algebras are inductive types

We will now show the other direction of the correspondence: given an
initial $W$-algebra, we *recover* the type $W_A B$ *and its induction
principle*, albeit with a propositional computation rule.

<!--
```agda
open induction→initial using (WAlg ; is-initial-WAlg ; W-initial) public

module initial→induction {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') (alg : WAlg A B) (init : is-initial-WAlg A B alg) where
  open induction→initial A B using (_W→_ ; idW ; _W∘_)
  module _ where private
```
-->

It's easy to invert the construction of `W-algebra`{.Agda} to obtain a
type `W'`{.Agda} and a candidate "constructor" `sup'`{.Agda}, by
projecting the corresponding components from the given $W$-algebra.

```agda
    W' : Type _
    W' = alg .fst

    sup' : (a : A) (b : B a → W') → W'
    sup' a b = alg .snd (a , b)
```

<!--
```agda
  open Σ alg renaming (fst to W' ; snd to sup')
```
-->

We will now show that `W'` satisfies the induction principle of $W_A B$.
To that end, suppose we have a predicate $P : W' \to \ty$, the
*motive* for induction, and a function — the *method* $m$ — showing
$P(\rm{sup}(a, f))$ given the data of the constructor $a : A$, $f :
(b : B\, a) \to W'$, and the induction hypotheses $f' : (b : B\, a) \to
P(f b)$.

```agda
  module
    _ (P : W' → Type (ℓ ⊔ ℓ'))
      (psup : ∀ {a f} (f' : (b : B a) → P (f b)) → P (sup' (a , f)))
    where
```

The first part of the construction is observing that $m$ is precisely
what is needed to equip the *total space* $\Sigma_{x : W'} P(x)$ of the
motive $P$ with $W$-algebra structure.  Correspondingly, we call this a
"total algebra" of $P$, and write it $\int P$.

```agda
    total-alg : WAlg A B
    total-alg .fst = Σ[ x ∈ W' ] P x
    total-alg .snd (x , ff') = sup' (x , fst ∘ ff') , psup (snd ∘ ff')
```

By our assumed initiality of $W'$, we then have a $W$-algebra morphism
$e : W' \to \int P$.

<!--
```agda
    private module _ where private
```
-->

```agda
      elim-hom : alg W→ total-alg
      elim-hom = init total-alg .centre
```

To better understand this, we can write out the components of this map.
First, we have an underlying function $W' \to \int P$, which sends an
element $x : W'$ to a pair $(i, d)$, with $i : W'$ and $d : P(i)$. Since
$i$ indexes a fibre of $P$, we refer to it as the `index`{.Agda} of the
result; the returned element $d$ is the `datum`{.Agda}.

```agda
      index : W' → W'
      index x = elim-hom .fst x .fst

      datum : ∀ x → P (index x)
      datum x = elim-hom .fst x .snd
```

<!--
```agda
    open is-contr (init total-alg) renaming (centre to elim-hom)
    module _ (x : W') where
      open Σ (elim-hom .fst x) renaming (fst to index ; snd to datum) public
```
-->

We also have the equation expressing that `elim-hom`{.Agda} is an
algebra map, which says that `index`{.Agda} and `datum`{.Agda} both
commute with supremum, where the second identification depends on the
first.

```agda
    beta
      : (a : A) (f : (x : B a) → W')
      → (index (sup' (a , f)) , datum (sup' (a , f)))
        ≡ (sup' (a , index ∘ f) , psup (datum ∘ f))
    beta a f = happly (elim-hom .snd) (a , f)
```

The datum part of `elim-hom`{.Agda} is *almost* what we want, but it's
not quite a section of $P$. To get the actual elimination principle,
we'll have to get rid of the `index`{.Agda} in its type. The insight now
is that, much like a [[total category]] admits a projection [[functor]]
to the base, the total *algebra* of $P$ should admit a projection
*morphism* to the base $W'$.

The composition
$$
W' \xto{e} \smallint P \xto{\pi} W'
$$
would then be an algebra morphism, inhabiting the contractible type $W'
\to W'$, which is also inhabited by the identity. But note that the
function part of this composition is exactly $i$, so we obtain a
homotopy $\phi : i \is \id$.

```agda
    φ : ∀ x → index x ≡ x
    φ = happly (ap fst htpy) module φ where
      πe : alg W→ alg
      πe .fst           = index
      πe .snd i (a , z) = beta a z i .fst

      htpy = is-contr→is-prop (init alg) πe idW
```

We can then define the eliminator $e' : \forall x, P\, x$ at $w : W'$ by
transporting $d(w) : P(i\, w)$ along $\phi$. Since we'll want to
characterise the value of $e'(\rm{sup}\, f)$ using the second component
of $\beta$, we can not directly define $\phi$ in terms of the
composition $\pi \circ e$. Instead, we equip $i$ with a bespoke algebra
structure, where the proof that $i(\rm{sup}\, f) = \rm{sup}\, (i \circ
f)$ comes from the *first* component of $\beta$.

```agda
    elim : ∀ x → P x
    elim w = subst P (φ w) (datum w)
```

Since the construction of $\phi$ works at the level of algebra
morphisms, rather than their underlying functions, we obtain a coherence
$\psi$, fitting in the diagram below.

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  {\rm{sup}\,(i \circ f)} \&\& {i(\rm{sup}\, f)} \\
  \\
  \&\& {\rm{sup} f}
  \arrow["{\beta_{f}\inv}", from=1-1, to=1-3]
  \arrow[""{name=0, anchor=center, inner sep=0}, "{\ap{\rm{sup}}{(\phi \circ f)}}"', from=1-1, to=3-3]
  \arrow["{\phi_{\rm{sup}\, f}}", from=1-3, to=3-3]
  \arrow["\psi"{description}, draw=none, from=1-3, to=0]
\end{tikzcd}\]
~~~

To show that $e'$ commutes with $\rm{sup}$, we can then perform a short
calculation using the second component of $\beta$, the coherence $\psi$,
and some stock facts about substitution.

```agda
    β : (a : A) (f : (x : B a) → W') → elim (sup' (a , f)) ≡ psup (elim ∘ f)
    β a f =
      let
        ψ : ∀ a f → sym (ap fst (beta a f)) ∙ φ (sup' (a , f)) ≡ ap sup'' (funext λ i → φ (f i))
        ψ a z = square→commutes (λ i j → φ.htpy j .snd (~ i) (a , z)) ∙ ∙-idr _
      in
        subst P (φ (sup'' f)) ⌜ datum (sup' (a , f)) ⌝                               ≡⟨ ap! (from-pathp⁻ (ap snd (beta a f))) ⟩
        subst P (φ (sup'' f)) (subst P (sym (ap fst (beta a f))) (psup (datum ∘ f))) ≡⟨ sym (subst-∙ P _ _ _) ∙ ap₂ (subst P) (ψ a f) refl ⟩
        subst P (ap sup'' (funext λ z → φ (f z))) (psup (datum ∘ f))                 ≡⟨ nat index datum (funext φ) a f ⟩
        psup (λ z → subst P (φ (f z)) (datum (f z)))                                 ∎
```

<!--
```agda
      where
      sup'' : ∀ {a} (f : B a → W') → W'
      sup'' f = sup' (_ , f)


      nat-t : (ix : W' → W') (h : ix ≡ id) (dt : ∀ x → P (ix x)) → _
      nat-t ix h dt =
        ∀ a (f : B a → W')
        → subst P (ap sup'' (funext λ z → happly h (f z))) (psup (dt ∘ f))
        ≡ psup (λ z → subst P (happly h (f z)) (dt (f z)))

      nat : ∀ ix dt h → nat-t ix h dt
      nat ix dt h = J (λ ix h → ∀ dt → nat-t ix (sym h) dt)
        (λ dt a f → Regularity.fast! refl)
        (sym h) dt
```
-->
