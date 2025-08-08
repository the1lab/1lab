<!--
```agda
open import 1Lab.Path.Reasoning
open import 1Lab.Reflection hiding (_!_ ; absurd ; lookup)
open import 1Lab.Prelude

open import Data.Fin.Properties
open import Data.Wellfounded.W
open import Data.Fin.Closure
open import Data.Bool.Base
open import Data.Dec.Base
open import Data.Fin.Base
open import Data.Sum.Base
open import Data.Bool

open hlevel-projection
```
-->

```agda
module Data.Set.Material where
```

# The cumulative hierarchy of iterative sets {defines="cumulative-hierarchy iterative-set"}

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A A' B B' C : Type ℓ
```
-->

Following Gylterud and Stenholm [-@Gylterud:sets], we define the
**cumulative hierarchy** of material [[sets]] as a *subtype* of a
[[W-type]], giving us better definitional control of the *type of
members* of a set than is possible with the [higher-inductive
construction]. The type $V$ of sets we construct here will then be
useful as a *set-truncated universe of sets*, since (unlike an
inductive-recursive universe), it can be populated post-hoc with a
definitional encoding for any type which injects into a material set.

[higher-inductive construction]: Data.Set.Material.HIT.html

Throughout this page, we will occasionally need to explicitly refer to
universe levels, but at most one; we will reserve the cursive $\ell$ for
this. We start by defining the type $V'_{\ell}$ of "multisets" as a
[[W-type]] with labels given by an arbitrary type $T : \ty_\ell$, and
where the branching factor for the constructor labelled $T$ is just $T$
itself.

```agda
private
  V' : (l : Level) → Type (lsuc l)
  V' l = W (Type l) (λ x → x)
```

We have a good understanding of [paths in W-types], but for this
specific construction, univalence lets us do better: the type of
identities between multisets $w, w' : V'$ is given by the **fibrewise
equivalences** between their `subtree`{.Agda}s.

[paths in W-types]: Data.Wellfounded.W.html#path-spaces-of-w-types

```agda
  veq : V' ℓ → V' ℓ → Type _
  veq w w' = (x : V' _) → fibre (subtree w) x ≃ fibre (subtree w') x
```

For a multiset $w : V'$, we think of the fibres of its `subtree`{.Agda}
function as a *membership* correspondence, where
$\operatorname{subtree}(w)^*(x)$ records "the ways for $x$ to belong to
$w$". At this stage, there may be multiple such ways, but we can still
think of `veq`{.Agda} as saying that $w$ and $w'$ *agree on their
containment of all other sets*. The theorem that `veq`{.Agda} is the
identity family for multisets is then a sort of extensionality
principle.

<details>
<summary>The proof that `veq`{.Agda} is the identity family for
`V'`{.Agda} is a lengthy, but uninspiring, calculation.</summary>

```agda
  abstract
    path≃veq : (x y : V' ℓ) → (x ≡ y) ≃ veq x y
    path≃veq (sup x f) (sup y g) =
      sup x f ≡ sup y g
        ≃⟨ WPath.Path≃Code (sup x f) (sup y g) ⟩
      Σ[ p ∈ x ≡ y ] (∀ {x y} → PathP (λ i → p i) x y → WPath.Code (f x) (g y))
        ≃˘⟨ Σ-ap-fst (ua , univalence⁻¹) ⟩
      Σ[ e ∈ x ≃ y ] (∀ {x y} → PathP (λ i → ua e i) x y → WPath.Code (f x) (g y))
        ≃⟨ Σ-ap-snd (λ e → Π'-ap-cod λ x → Π'-ap-cod λ y → Π-ap-dom (ua-pathp≃path _)) ⟩
      Σ[ e ∈ x ≃ y ] (∀ {x y} → e .fst x ≡ y → WPath.Code (f x) (g y))
        ≃⟨ Σ-ap-snd (λ e → Π'-ap-cod λ x → Π'-ap-cod λ y → Π-ap-cod λ p → Equiv.inverse (WPath.Path≃Code (f x) (g y))) ⟩
      Σ[ e ∈ x ≃ y ] (∀ {x y} → e .fst x ≡ y → f x ≡ g y)
        ≃˘⟨ Σ-ap-snd (λ e → Π²-impl≃) ⟩
      Σ[ e ∈ x ≃ y ] (∀ x y → e .fst x ≡ y → f x ≡ g y)
        ≃˘⟨ Σ-ap-snd (λ e → Π-ap-cod λ x → curry≃) ⟩
      Σ[ e ∈ x ≃ y ] (∀ x → ((y , _) : Σ[ y ∈ y ] (e .fst x ≡ y)) → f x ≡ g y)
        ≃⟨ Σ-ap-snd (λ e → Π-ap-cod λ x → Π-contr-eqv (hlevel 0)) ⟩
      Σ[ e ∈ x ≃ y ] (∀ x → f x ≡ g (e .fst x))
        ≃⟨ equiv-over≃fibrewise-equiv f g ⟩
      veq (sup x f) (sup y g)
        ≃∎
```

</details>

If we are to carve out a subtype of `V'`{.Agda} which is a [[set]],
then, it will suffice to find one for which the membership
correspondence is valued in [[propositions]], i.e. is a relation. The
fibrewise-propositional functions are called [[embeddings]], so it
suffices to consider the subtype `V`{.Agda} of `V'`{.Agda} consisting of
the multisets which are everywhere embeddings: the **iterative
embeddings**.

```agda
is-iterative-embedding : V' ℓ → Type (lsuc ℓ)
is-iterative-embedding (sup x f) = is-embedding f × (∀ y → is-iterative-embedding (f y))
```

By induction, being an iterative embedding is a proposition, because it
pairs a proposition (the outermost `subtree`{.Agda}-assigning function
is an embedding) with a product of propositions (each subtree is an
iterative embedding).

<!--
```agda
is-iterative-embedding-is-prop : (x : V' ℓ) → is-prop (is-iterative-embedding x)

instance
  hlevel-proj-is-iterative-embedding : hlevel-projection (quote is-iterative-embedding)
  hlevel-proj-is-iterative-embedding .has-level   = quote is-iterative-embedding-is-prop
  hlevel-proj-is-iterative-embedding .get-level _ = pure (lit (nat 1))
  hlevel-proj-is-iterative-embedding .get-argument (_ h∷ x v∷ []) = pure x
  hlevel-proj-is-iterative-embedding .get-argument _              = typeError []

is-iterative-embedding-is-prop (sup x f) = hlevel 1
```
-->

:::{.definition #material-set}
A **material set** is an element of `V`{.Agda}.

```agda
record V (l : Level) : Type (lsuc l) where
  no-eta-equality
  constructor set
  field
    tree : V' l
    uniq : is-iterative-embedding tree
```
:::

<!--
```agda
{-# INLINE V.constructor #-}

open V public

ap-set : {x y : V ℓ} → x .tree ≡ y .tree → x ≡ y
ap-set α i .tree = α i
ap-set {x = x} {y} α i .uniq = is-prop→pathp (λ i → is-iterative-embedding-is-prop (α i)) (x .uniq) (y .uniq) i

private
  prj : (w : V' ℓ) → is-iterative-embedding w → is-embedding (subtree w)
  prj (sup _ _) (p , _) = p
```
-->

We can then prove that `V`{.Agda} is a set, since `veq`{.Agda} for
iterative embeddings is a proposition.

```agda
instance abstract
  H-Level-V : ∀ {ℓ n} → H-Level (V ℓ) (2 + n)
  H-Level-V = basic-instance 2 $ retract→is-hlevel 2
    (uncurry V.constructor) (λ v → v .tree , v .uniq) (λ x → ap-set refl)
    λ (x , α) (y , β) → Equiv→is-hlevel 1 (Equiv.inverse Σ-pathp≃)
      (Σ-is-hlevel 1 (Equiv→is-hlevel 1 (path≃veq x y)
      (Π-is-hlevel 1 (λ v → ≃-is-hlevel 1 (prj _ α _) (prj _ β _))))
      λ _ → hlevel 1)
```

<!--
```agda
abstract
  tree-is-embedding : is-embedding {A = V ℓ} V.tree
  tree-is-embedding x (s , α) (t , β) = Σ-prop-path
    (λ y → Equiv→is-hlevel 1 (path≃veq _ _) (Π-is-hlevel 1 λ z →
      ≃-is-hlevelˡ 0 (prj _ (y .uniq) _)))
    (ap-set (α ∙ sym β))

-- We redefine these so we can be precise about the hlevel-projection
-- instance for El on V (we need an explicit matching function instead
-- of using a with-abstraction to refer to it by name) instead of
-- thinking that *every* label must be a set because it comes from V
-- and then having a really mysterious error message.
--
-- They can't be private because they're used in the Automation module.
--
-- It's also defined for an entire S : V with a named local helper
-- (instead of for S .tree : V') so we can write a DISPLAY form to print
-- v-label as El.
--
-- It's important that S is bound in the lhs of v-label
-- (thus again in the λ-lifting of v-label.impl) so the normal form of
-- v-label looks like
--
--    v-label.impl {ℓ} S (S .tree)
-- whence we can recover ℓ and S with a display form.

v-label : V ℓ → Type ℓ
v-label {ℓ = ℓ} S = impl (S .tree) module v-label where
  impl : V' ℓ → Type ℓ
  impl (sup x f) = x

pattern v-label-args S = _ h∷ S v∷ def (quote tree) _ v∷ []

private
  v-subtree : (x : V ℓ) → v-label x → V' ℓ
  v-subtree S with S .tree
  ... | sup x f = f

instance
  Underlying-V : Underlying (V ℓ)
  Underlying-V = record { ⌞_⌟ = λ v → v-label v }

_∈ⱽ_ : (x y : V ℓ) → Type (lsuc ℓ)
x ∈ⱽ y with y .tree
... | sup A f = fibre f (x .tree)

instance
  Membership-V : Membership (V ℓ) (V ℓ) _
  Membership-V = record { _∈_ = _∈ⱽ_ }
```
-->

We can define a 'constructor' for `V`{.Agda} which takes the supremum of
an embedding into `V`{.Agda}. We could then go on to show that
`supⱽ`{.Agda} actually *does* generate `V`{.Agda}, i.e. exhibit an
induction principle saying that covering `supⱽ`{.Agda} suffices to cover
all of `V`{.Agda}, but this will not be necessary.

```agda
supⱽ : (T : Type ℓ) (f : T ↪ V ℓ) → V ℓ
{-# INLINE supⱽ #-}
supⱽ T f = record
  { tree = sup T (λ x → f .fst x .tree)
  ; uniq = ∘-is-embedding tree-is-embedding (f .snd) , λ y → f .fst y .uniq
  }
```

<details>
<summary>When formalising constructions with material sets, it will be
convenient to have syntax for `supⱽ`{.Agda} where the function is only
assumed to be an injection (which suffices since `V`{.Agda} is a set),
and which lets us specify this data separately from the
function.</summary>

```agda
-- Efficiency note: because composing embeddings generates pretty
-- horrible stuff, this module *needs* the function above (and mkⱽ
-- below) to be INLINE, so the normal forms of codes in V are compact.

record mkV ℓ : Type (lsuc ℓ) where
  field
    Elt : Type ℓ
    idx : Elt → V ℓ
    inj : injective idx

  mkⱽ : V ℓ
  {-# INLINE mkⱽ #-}
  mkⱽ = supⱽ Elt (idx , injective→is-embedding! inj)

open mkV public
```

</details>

We will, however, define a principle of "$\in$-induction", saying that,
if you can show $P(a)$ under the assumption that $P(x)$ for every $x \in
a$, then $P$ holds of arbitrary sets--- in order words, that the $\in$
relation is [[well-founded]]. As usual, this implies that the membership
relation is irreflexive.

```agda
∈-induction
  : ∀ {ℓ'} (P : V ℓ → Type ℓ')
  → ({a : V ℓ} → ({x : V ℓ} → x ∈ a → x ∈ P) → a ∈ P)
  → (x : V ℓ) → x ∈ P
∈-induction {ℓ = ℓ} P pmem S = subst P (ap-set refl) (go (S .tree) (S .uniq)) where
  go : (x : V' ℓ) (iie : is-iterative-embedding x) → P (set x iie)
  go (sup x f) (fe , su) = pmem λ {y} (j , α) →
    subst P (ap-set α) (go (f j) (su j))

∈-irrefl : (x : V ℓ) → x ∈ x → ⊥
∈-irrefl = ∈-induction _ λ {a} ind a∈a → ind a∈a a∈a
```

Finally, we can also define pattern-matching functions to project the
"label" and "subtree" from a material set. The subtree function
`_!_`{.Agda} is, by construction, an embedding (hence, an injection),
and we can pair it with that proof to obtain for each material set an
embedding `lookup`{.Agda} from its type of members back into the
cumulative hierarchy.

```agda
_!_ : (S : V ℓ) → ⌞ S ⌟ → V ℓ
S ! x with S .tree | S .uniq
... | sup A f | _ , φ = set (f x) (φ x)

!-inj : (S : V ℓ) {x y : ⌞ S ⌟} → S ! x ≡ S ! y → x ≡ y
!-inj S α with S .tree | S .uniq
... | sup x f | φ , _ = ap fst (φ _ (_ , ap tree α) (_ , refl))

lookup : (S : V ℓ) → ⌞ S ⌟ ↪ V ℓ
lookup S .fst = S !_
lookup S .snd = injective→is-embedding! (!-inj S)
```

## $V$ as a universe

The "type-of-members" projection from $V$ allows us to think of it as a
*universe* of [[h-sets|set]], though one which, unlike the built-in
universes of Agda, requires us to explicitly *decode* an element of the
universe into a type[^tarski]. To make this interpretation explicit, we
will sometimes refer to the type-of-members projection by `El`{.Agda},
which is the traditional name for the decoding family of a Tarski
universe.

[^tarski]:
    In the type-theoretic literature, these universes are termed "à la
    Tarski", or simply "Tarski universes". If there is no decoding type
    family, and the elements of a universe are *literally* types, then
    they are called "à la Russell", or "Russell universes".

```agda
Elⱽ : V ℓ → Type ℓ
Elⱽ V = ⌞ V ⌟

abstract
  El-is-set : (x : V ℓ) → is-set (Elⱽ x)
  El-is-set x = embedding→is-hlevel 1 (lookup x .snd) (hlevel 2)
```

From this perspective, we think of constructing a material set with a
specific type of members as showing that `V`{.Agda} is closed under a
specific type-theoretic connective. To this end, the following
"realignment" principle will be useful: it says that if $x$ is a
material set and $f : T \mono \El x$ is an injection, we can obtain a
material set which definitionally decodes to $T$.

```agda
realignⱽ : (x : V ℓ) {T : Type ℓ} (e : T → Elⱽ x) → injective e → V ℓ
{-# INLINE realignⱽ #-}
realignⱽ x {T} f α = mkⱽ λ where
  .Elt   → T
  .idx i → x ! f i
  .inj i → α (!-inj x i)

_ : ∀ {x : V ℓ} {T} {e : T → Elⱽ x} {p : injective e}
  → Elⱽ (realignⱽ x e p) ≡ T
_ = refl
```

<!--
```agda
-- We defined the v-label wrapper to write *this* instance, since if we
-- just reused 'label' it would spuriously be applied to the type of
-- labels of an arbitrary W-type (and then fail when the thing it's
-- applied to isn't the 'tree' projection from a V-set).

instance
  hlevel-projection-v-label : hlevel-projection (quote v-label.impl)
  hlevel-projection-v-label .has-level    = quote El-is-set
  hlevel-projection-v-label .get-level _  = pure (lit (nat 2))
  hlevel-projection-v-label .get-argument a with a
  ... | v-label-args x = pure x
  ... | _              = do
    `a ← quoteTC a >>= normalise
    typeError [ termErr `a ]

-- We also need the wrapper for this display form, since we can't write
-- a display form for v-label (S .tree).
{-# DISPLAY v-label.impl {ℓ} S _ = Elⱽ {ℓ} S #-}
{-# DISPLAY v-label {ℓ} S = Elⱽ {ℓ} S #-} -- for printing in Simplified or Instantiated rewriting levels

-- Test that the instance works:
private
  _ : {x : V ℓ} → is-set ⌞ x ⌟
  _ = hlevel 2

lookup→member : (S : V ℓ) {x : V ℓ} {j : ⌞ S ⌟} → (S ! j) ≡ x → x ∈ S
lookup→member S p with S .tree | S .uniq
... | sup x f | _ = _ , ap tree p
```
-->

## Constructing material sets

Since the empty function is an embedding, the empty *type* has a code in
`V`{.Agda}, which is 'the empty set' --- it has no members.

```agda
∅ⱽ : V ℓ
∅ⱽ = supⱽ (Lift _ ⊥) ((λ ()) , (λ { _ (() , _) }))
```

Similarly, since any function from the unit type is injective, if you
already have a material set $x$, you can construct the set $\{x\}$. Note
that this is *itself* an embedding into `V`{.Agda}.

```agda
oneⱽ : V ℓ → V ℓ
oneⱽ v = mkⱽ λ where
  .Elt   → Lift _ ⊤
  .idx _ → v
  .inj _ → refl

one-inj : {x y : V ℓ} → oneⱽ x ≡ oneⱽ y → x ≡ y
one-inj x = ap-set (ap₂ (λ e y → (e ! y) .tree) x (to-pathp refl))
```

Moreover, we can prove that $x$ is distinct from $\{x\}$ by showing that
identifying them would contradict irreflexivity of the $\in$-relation.

```agda
x≠[x] : (x : V ℓ) → x ≡ oneⱽ x → ⊥
x≠[x] x p = ∈-irrefl x (subst (x ∈_) (sym p) (lift tt , refl))
```

We can't, in general, write a function that puts *two* arguments into a
material set: if you fed it the same set twice, it would end up
constructing "$\{x, x\}$", and we can not show that the `member`{.Agda}
function for this pathological example is an injection. However, we
*can* write a function that packs two *distinct* values into a material
set--- forming $\{x, y\}$ under the assumption that $x \ne y$.

```agda
twoⱽ : (x y : V ℓ) → x ≠ y → V ℓ
twoⱽ x y d = mkⱽ λ where
  .Elt → Lift _ Bool
  .idx (lift true)  → x
  .idx (lift false) → y

  .inj {lift true}  {lift true}  p → refl
  .inj {lift true}  {lift false} p → absurd (d p)
  .inj {lift false} {lift true}  p → absurd (d (sym p))
  .inj {lift false} {lift false} p → refl
```

<details>
<summary>
We will need later that `two`{.Agda} is *almost* an injection, i.e. that
if you have $x_1 \ne y_0$ then $\{x_0,y_0\} = \{x_1,y_1\}$ implies $x_0
= x_1$ and $y_0 = y_1$.
</summary>

```agda
two-inj
  : {x₀ x₁ y₀ y₁ : V ℓ} {p : x₀ ≠ y₀} {q : x₁ ≠ y₁} (r : x₁ ≠ y₀)
  → twoⱽ x₀ y₀ p ≡ twoⱽ x₁ y₁ q
  → (x₀ ≡ x₁) × (y₀ ≡ y₁)
two-inj {x₀ = x₀} {x₁} {y₀} {y₁} {d₀} {d₁} ah α = done where
  p : Lift _ Bool ≡ Lift _ Bool
  p = ap Elⱽ α

  q : {a b : Lift _ Bool} → transport p a ≡ b
    → subtree (twoⱽ x₀ y₀ d₀ .tree) a ≡ subtree (twoⱽ x₁ y₁ d₁ .tree) b
  q a i = v-subtree (α i) (to-pathp {A = λ i → p i} a i)

  rem₁ : ∀ x → transport p (lift x) ≡ lift x
  rem₁ x =
    let
      e = ≃-ap Lift-≃ Lift-≃ .fst (path→equiv p)

      β : transport p (lift false) .lower ≡ false
      β = dec→dne λ pt≠t → ah (sym (ap-set (q (ap lift (ne→is-not pt≠t)))))
    in ap lift $ bool-equiv-id e _ x β

  abstract
    done : (x₀ ≡ x₁) × (y₀ ≡ y₁)
    done = ap-set (q (rem₁ true)) , ap-set (q (rem₁ false))
```

</details>

We can construct a *successor* operation on material sets, too, such
that $y \in \operatorname{suc}(x)$ if $y = x$ or $y \in x$. This is a
legitimate construction because $x$ is distinct from all of its members.

```agda
sucⱽ : V ℓ → V ℓ
sucⱽ x = mkⱽ λ where
  .Elt → ⊤ ⊎ Elⱽ x

  .idx (inl tt) → x
  .idx (inr j)  → x ! j

  .inj {inl _} {inl _} p → refl
  .inj {inl _} {inr _} p → absurd (∈-irrefl x (lookup→member x (sym p)))
  .inj {inr _} {inl _} p → absurd (∈-irrefl x (lookup→member x p))
  .inj {inr _} {inr _} p → ap inr (!-inj x p)
```

By iterating successors of the empty set, we can accurately encode the
natural numbers. We note that the type of members of `encoden`{.Agda} at
$n$ is equivalent to $\operatorname{Fin}(n)$, and, since `Fin`{.Agda} is
also injective, we can show `encoden`{.Agda} is itself injective.

```agda
Natⱽ : V lzero
Natⱽ = mkⱽ (mkV.constructor _ encoden encoden-inj) where
  encoden : Nat → V ℓ
  encoden zero    = ∅ⱽ
  encoden (suc x) = sucⱽ (encoden x)

  encoden-inj : ∀ {ℓ} → injective (encoden {ℓ})
  encoden-inj {ℓ} p = Fin-injective (Equiv.inverse (lemma _) ∙e path→equiv (ap Elⱽ p) ∙e lemma _) where
    lemma : ∀ n → Elⱽ (encoden {ℓ} n) ≃ Fin n
    lemma zero    = (λ ()) , record { is-eqv = λ x → absurd (Fin-absurd x) }
    lemma (suc n) = ⊎-ap id≃ (lemma n) ∙e Equiv.inverse Finite-successor
```

## Pairing

Using the constructors `∅ⱽ`{.Agda}, `oneⱽ`{.Agda} and `twoⱽ`{.Agda}, we
can construct the ordered pairing of any two material sets $a$, $b$, by
wrapping them in sufficient brackets to make them distinct.
Specifically, we code for $(a, b)$ as $$\{\{\{a\},\emptyset\},\{\{b\}\}\}$$.

<details>
<summary>This construction requires a few annoying lemmas distinguishing
`∅ⱽ`{.Agda}, `oneⱽ`{.Agda} and `twoⱽ`{.Agda}, which are all by how we
can distinguish their types of members.</summary>

```agda
abstract
  one≠∅ : {x : V ℓ} → oneⱽ x ≠ ∅ⱽ
  one≠∅ p = subst ⌞_⌟ (ap Elⱽ p) (lift tt) .lower

  one≠two : ∀ {x y z : V ℓ} {p} → oneⱽ x ≠ twoⱽ y z p
  one≠two p = true≠false (ap lower (subst is-prop (ap Elⱽ p) (hlevel 1) _ _))
```

</details>

```agda
pair : V ℓ → V ℓ → V ℓ
pair a b =
  twoⱽ
    (twoⱽ (oneⱽ a) ∅ⱽ one≠∅)
    (oneⱽ (oneⱽ b))
  (one≠two ∘ sym)
```

The absurd number of brackets is required to meet the side-condition for
`two-inj`{.Agda}, which lets us show that this is an injection from $V
\times V$ into $V$.

```agda
abstract
  pair-inj
    : {x x' y y' : V ℓ}
    → pair x y ≡ pair x' y' → Path (V ℓ × V ℓ) (x , y) (x' , y')
  pair-inj α =
    let
      (p1 , p2) = two-inj (one≠two ∘ sym) α
      (p1' , _) = two-inj one≠∅ p1
    in one-inj p1' ,ₚ one-inj (one-inj p2)
```

Using this ordered pairing structure, we can show that $V$ is closed
under dependent sum: if $X$ is a $V$-set and $Y$ is a family of $V$-sets
over $X$, the type $\sum_{i : \El X} \El (Y(i))$ injects into $V$ by
sending each $(a,b)$ to $\{a, b\}$. The proof that this is an injection
is slightly complicated by the type dependency, but it's not
unmanageable.

```agda
Σⱽ : (X : V ℓ) (Y : Elⱽ X → V ℓ) → V ℓ
Σⱽ x y = mkⱽ λ where
  .Elt         → Σ[ i ∈ Elⱽ x ] Elⱽ (y i)
  .idx (a , b) → pair (x ! a) (y a ! b)
```

<details>
<summary>We leave the proof that this is an injection in this
`<details>`{.html} block.</summary>

```agda
  .inj {a , b} {a' , b'} α →
    let
      p1 , p2 = Σ-pathp.from (pair-inj α)

      p : a ≡ a'
      p = !-inj x p1

      q : (y a ! b) ≡ (y a ! subst (Elⱽ ∘ y) (sym p) b')
      q = subst₂ (λ e b' → (y a ! b) ≡ (y e ! b')) (sym p) (to-pathp refl) p2
    in Σ-pathp (!-inj x p1) (to-pathp⁻ (!-inj (y a) q))
```

</details>

```agda
_ : ∀ {A : V ℓ} {B} → Elⱽ (Σⱽ A B) ≡ (Σ[ a ∈ Elⱽ A ] Elⱽ (B a))
_ = refl
```

## Separation and power sets

Under our assumption of [[propositional resizing]], we can show that any
property $P$ of a $V$-set $x$ is *separable*: we have a set $\name{P} =
\{e \in x\, |\, P(e)\}$ whose elements are precisely the elements of $x$
that satisfy $P$.

```agda
subsetⱽ : (x : V ℓ) → (Elⱽ x → Ω) → V ℓ
subsetⱽ v f = mkⱽ λ where
  .Elt         → Σ[ i ∈ v ] (i ∈ f)
  .idx (x , _) → v ! x
  .inj α       → Σ-prop-path! (!-inj v α)
```

More importantly, if we fix $x$, then we can *recover* the proposition
$P(e)$ we started with as "$e \in \name{P}$". This shows that, if $x$ is
held fixed, then `subsetⱽ`{.Agda} is an injection of $x \to \Omega$ into
$V$, and the entire [[power set]] of $x$ has a $V$-code.

```agda
subsetⱽ-inj : (x : V ℓ) (p q : Elⱽ x → Ω) → subsetⱽ x p ≡ subsetⱽ x q → p ≡ q
subsetⱽ-inj x p q α = funext λ ex →
  let
    same-ix : ∀ {a b} (p : PathP (λ i → Elⱽ (α i)) a b) → a .fst ≡ b .fst
    same-ix p = !-inj x (ap-set (λ i → (α i ! p i) .tree))
  in Ω-ua
    (λ a →
      let (ix , pix) = subst Elⱽ α (ex , a)
       in subst (_∈ q) (sym (same-ix {ex , a} {ix , pix} (to-pathp refl))) pix)
    (λ a →
      let (ix , pix) = subst Elⱽ (sym α) (ex , a)
       in subst (_∈ p) (same-ix {ix , pix} {ex , a} (to-pathp⁻ refl)) pix)

ℙⱽ : V ℓ → V ℓ
ℙⱽ x = mkⱽ λ where
  .Elt           → Elⱽ x → Ω
  .idx p         → subsetⱽ x p
  .inj {p} {q} α → subsetⱽ-inj _ _ _ α
```

## Function sets

To encode function sets, we will make use of `realignⱽ`{.Agda} and
closure of $V$ under power sets. When the codomain is a (family of)
[[sets]], the (dependent) function type $(x : A) \to B(x)$ embeds into
the type of predicates on $\sum_{x : A}B(x)$ by the map which sends each
function to its `graph`{.Agda}.

```agda
module _ {A : Type ℓ} {B : A → Type ℓ} where
  graph : (∀ x → B x) → (Σ[ a ∈ A ] B a → Ω)
  graph f (x , y) = elΩ (f x ≡ y)

  graph-inj
    : ⦃ _ : ∀ {x} → H-Level (B x) 2 ⦄
    → (f g : (x : A) → B x) → graph f ≡ graph g → f ≡ g
  graph-inj f g α = funext λ a →
    case subst (λ e → (a , f a) ∈ e) α (inc refl) of sym
```

The realignment principle then lets us obtain a definitional encoding
for dependent function types as a subset of the encoding of relations.

```agda
Πⱽ : (A : V ℓ) (B : Elⱽ A → V ℓ) → V ℓ
Πⱽ A B = realignⱽ (ℙⱽ (Σⱽ A B))
  graph (graph-inj _ _)

_ : ∀ {A : V ℓ} {B} → Elⱽ (Πⱽ A B) ≡ ((x : Elⱽ A) → Elⱽ (B x))
_ = refl
```

## Lifting and a $V$-code for $V$

Agda universes are not cumulative, but we can define a `Lift`{.Agda}ing
operation which codes for a type $X : \ty_\ell$ in some higher-levelled
universe, which we generically write as being $\ell \sqcup \ell'$. By
inserting these `Lift`{.Agda}s at every `sup`{.Agda} of a $V$-set, we
can also lift $V$-sets.

```agda
liftⱽ : ∀ ℓ' → V ℓ → V (ℓ ⊔ ℓ')
liftⱽ {ℓ = ℓ} ℓ' = wrap module liftⱽ where
  liftⱽ' : V' ℓ → V' (ℓ ⊔ ℓ')
  liftⱽ' (sup x f) = sup (Lift ℓ' x) (λ (lift i) → liftⱽ' (f i))
```

<details>
<summary>Using that `Lift`{.Agda} is an embedding, we can prove by an
inductive calculation that the recursive lifting `liftⱽ'`{.Agda} is also
an embedding.</summary>

```agda
  module l {x} {y} = Equiv (ap (Lift {ℓ} ℓ') {x} {y} , embedding→cancellable (Lift-is-embedding ℓ'))

  abstract
    inj' : (x y : V' ℓ) → (liftⱽ' x ≡ liftⱽ' y) ≃ (x ≡ y)
    inj' (sup x f) (sup y g) =
      liftⱽ' (sup x f) ≡ liftⱽ' (sup y g)
        ≃⟨ ap-equiv W-fixpoint ⟩
      (Lift ℓ' x , liftⱽ' ∘ f ∘ lower) ≡ (Lift ℓ' y , liftⱽ' ∘ g ∘ lower)
        ≃˘⟨ Σ-pathp≃ ⟩
      (Σ (Lift ℓ' x ≡ Lift ℓ' y) (λ p → PathP (λ i → p i → V' (ℓ ⊔ ℓ')) (liftⱽ' ∘ f ∘ lower) (liftⱽ' ∘ g ∘ lower)))
        ≃˘⟨ Σ-ap-fst (Equiv.inverse l.inverse) ⟩
      (Σ (x ≡ y) λ p → PathP (λ i → Lift ℓ' (p i) → V' (ℓ ⊔ ℓ')) (liftⱽ' ∘ f ∘ lower) (liftⱽ' ∘ g ∘ lower))
        ≃˘⟨ Σ-ap-snd (λ p → apd-equiv (λ i → Π-ap-dom Lift-≃)) ⟩
      (Σ (x ≡ y) λ p → PathP (λ i → p i → V' (ℓ ⊔ ℓ')) (liftⱽ' ∘ f) (liftⱽ' ∘ g))
        ≃⟨ Σ-ap-snd
            (λ p → funext-dep≃ e⁻¹ ∙e Π'-ap-cod (λ x → Π'-ap-cod λ _ → Π-ap-cod λ _ → inj' (f x) _) ∙e funext-dep≃) ⟩
      (Σ (x ≡ y) λ p → PathP (λ i → p i → V' ℓ) f g)
        ≃⟨ Σ-pathp≃ ⟩
      (x , f) ≡ (y , g)
        ≃˘⟨ ap-equiv W-fixpoint ⟩
      sup x f ≡ sup y g
        ≃∎

  emb : is-embedding liftⱽ'
  emb = cancellable→embedding (inj' _ _)
```

Because of our definition of $V$, we need a wrapper saying that
`liftⱽ'`{.Agda} sends iterative embeddings to iterative embeddings.

```agda
  go  : (w : V' ℓ) (u : is-iterative-embedding w) → V (ℓ ⊔ ℓ')
  goβ : (w : V' ℓ) (u : is-iterative-embedding w) → go w u .tree ≡ liftⱽ' w

  go (sup x f) (φ , r) .tree = liftⱽ' (sup x f)
  go (sup x f) (φ , r) .uniq =
    ∘-is-embedding (∘-is-embedding emb φ) (is-equiv→is-embedding (Lift-≃ .snd))
    , λ (lift y) → let it = go (f y) (r y) .uniq in subst is-iterative-embedding (goβ (f y) (r y)) it

  goβ (sup x f) (_ , _) = refl

  wrap : V ℓ → V (ℓ ⊔ ℓ')
  wrap S = go (S .tree) (S .uniq)

  is-inj : injective wrap
  is-inj α = ap-set (ap fst (emb _ (_ , sym (goβ _ _) ∙ ap tree α ∙ goβ _ _) (_ , refl)))

  ungo : (w : V' ℓ) (u : is-iterative-embedding w) → v-label (go w u) ≃ v-label (set w u)
  ungo (sup x f) u .fst = lower
  ungo (sup x f) u .snd = is-iso→is-equiv (iso lift (λ _ → refl) λ _ → refl)

  unraise : ∀ x → Elⱽ (wrap x) ≃ Elⱽ x
  unraise x = ungo (x .tree) (x .uniq)
  module unraise x = Equiv (unraise x)
```

</details>

Since `liftⱽ`{.Agda} is itself an embedding of $V_\ell$ onto $V_{\ell'}$
for any $\ell' > \ell$, we can obtain a definitional $V_{(1 + \ell)}$-code
for $V_\ell$.

```agda
Vⱽ : ∀ {ℓ} → V (lsuc ℓ)
Vⱽ {ℓ} = mkⱽ λ where
  .Elt → V ℓ
  .idx → liftⱽ _
  .inj → liftⱽ.is-inj _
```
