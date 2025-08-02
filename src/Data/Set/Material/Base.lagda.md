<!--
```agda
open import 1Lab.Path.Reasoning
open import 1Lab.Reflection hiding (_!_ ; absurd)
open import 1Lab.Prelude

open import Data.Fin.Properties
open import Data.Wellfounded.W
open import Data.Fin.Closure
open import Data.Bool.Base
open import Data.Dec.Base
open import Data.Fin.Base
open import Data.Bool

open hlevel-projection
```
-->

```agda
module Data.Set.Material.Base where
```

# The cumulative hierarchy as a subtype

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

We have a good understanding of paths in W-types, but for this specific
construction, univalence lets us do better: the type of identities
between multisets $w, w' : V'$ is given by the **fibrewise
equivalences** between their `subtree`{.Agda}s.

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
        ≃⟨ Σ-ap-snd (λ e → Iso→Equiv ((λ α _ _ p → α p) , iso _ (λ x → refl) (λ x → refl))) ⟩
      Σ[ e ∈ x ≃ y ] (∀ x y → e .fst x ≡ y → f x ≡ g y)
        ≃⟨ Σ-ap-snd (λ e → Π-ap-cod λ x → Iso→Equiv (uncurry , iso curry (λ x → refl) (λ x → refl))) ⟩
      Σ[ e ∈ x ≃ y ] (∀ x → ((y , _) : Σ[ y ∈ y ] (e .fst x ≡ y)) → f x ≡ g y)
        ≃⟨ Σ-ap-snd (λ e → Π-ap-cod λ x → Π-contr-eqv (hlevel 0)) ⟩
      Σ[ e ∈ x ≃ y ] (∀ x → f x ≡ g (e .fst x))
        ≃⟨ equiv-over≃fibrewise-equiv f g ⟩
      veq (sup x f) (sup y g)
        ≃∎
```

</details>

```agda
is-iterative-embedding : V' ℓ → Type (lsuc ℓ)
is-iterative-embedding (sup x f) = is-embedding f × (∀ y → is-iterative-embedding (f y))

is-iterative-embedding-is-prop : (x : V' ℓ) → is-prop (is-iterative-embedding x)

instance
  hlevel-proj-is-iterative-embedding : hlevel-projection (quote is-iterative-embedding)
  hlevel-proj-is-iterative-embedding .has-level   = quote is-iterative-embedding-is-prop
  hlevel-proj-is-iterative-embedding .get-level _ = pure (lit (nat 1))
  hlevel-proj-is-iterative-embedding .get-argument (_ h∷ x v∷ []) = pure x
  hlevel-proj-is-iterative-embedding .get-argument _              = typeError []

is-iterative-embedding-is-prop (sup x f) = hlevel 1

record V (l : Level) : Type (lsuc l) where
  no-eta-equality
  constructor set
  field
    tree : V' l
    uniq : is-iterative-embedding tree

{-# INLINE V.constructor #-}

open V

ap-set : {x y : V ℓ} → x .tree ≡ y .tree → x ≡ y
ap-set α i .tree = α i
ap-set {x = x} {y} α i .uniq = is-prop→pathp (λ i → is-iterative-embedding-is-prop (α i)) (x .uniq) (y .uniq) i

private
  prj : (w : V' ℓ) → is-iterative-embedding w → is-embedding (subtree w)
  prj (sup _ _) (p , _) = p

instance abstract
  H-Level-V : ∀ {ℓ n} → H-Level (V ℓ) (2 + n)
  H-Level-V = basic-instance 2 $ retract→is-hlevel 2
    (uncurry V.constructor) (λ v → v .tree , v .uniq) (λ x → ap-set refl)
    λ (x , α) (y , β) → Equiv→is-hlevel 1 (Equiv.inverse Σ-pathp≃)
      (Σ-is-hlevel 1 (Equiv→is-hlevel 1 (path≃veq x y)
      (Π-is-hlevel 1 (λ v → ≃-is-hlevel 1 (prj _ α _) (prj _ β _))))
      λ _ → hlevel 1)

abstract
  tree-is-embedding : is-embedding {A = V ℓ} V.tree
  tree-is-embedding x (s , α) (t , β) = Σ-prop-path
    (λ y → Equiv→is-hlevel 1 (path≃veq _ _) (Π-is-hlevel 1 λ z →
      ≃-is-hlevelˡ 0 (prj _ (y .uniq) _)))
    (ap-set (α ∙ sym β))

open V

private
  -- we redefine these so we can be precise about the hlevel-projection
  -- instance for El on V (we need an explicit matching function instead
  -- of using a with-abstraction to refer to it by name) instead of
  -- thinking that *every* label must be a set because it comes from V
  -- and then having a really mysterious error message
  v-label : V' ℓ → Type ℓ
  v-label (sup x f) = x

  v-subtree : (x : V' ℓ) → v-label x → V' ℓ
  v-subtree (sup x f) = f

  pattern v-label-args x = _ h∷ def (quote tree) (_ h∷ x v∷ []) v∷ []

instance
  Underlying-V : Underlying (V ℓ)
  Underlying-V = record { ⌞_⌟ = λ v → v-label (v .tree) }

_!_ : (S : V ℓ) → ⌞ S ⌟ → V ℓ
_!_ {ℓ = ℓ} S x with S .tree | S .uniq
... | sup A f | _ , φ = set (f x) (φ x)

_∈ⱽ_ : (x y : V ℓ) → Type (lsuc ℓ)
x ∈ⱽ y with y .tree
... | sup A f = fibre f (x .tree)

instance
  Membership-V : Membership (V ℓ) (V ℓ) _
  Membership-V = record { _∈_ = _∈ⱽ_ }

!-inj : (S : V ℓ) {x y : ⌞ S ⌟} → S ! x ≡ S ! y → x ≡ y
!-inj S α with S .tree | S .uniq
... | sup x f | φ , _ = ap fst (φ _ (_ , ap tree α) (_ , refl))

supv : (T : Type ℓ) (f : T ↪ V ℓ) → V ℓ
{-# INLINE supv #-}
supv T f = record
  { tree = sup T (λ x → f .fst x .tree)
  ; uniq = ∘-is-embedding tree-is-embedding (f .snd) , λ y → f .fst y .uniq
  }

record mkV ℓ : Type (lsuc ℓ) where
  field
    Elt : Type ℓ
    idx : Elt → V ℓ
    inj : injective idx

  mkv : V ℓ
  {-# INLINE mkv #-}
  mkv = supv Elt (idx , injective→is-embedding! inj)

open mkV

subset : (S : V ℓ) → ⌞ S ⌟ ↪ V ℓ
subset S .fst = S !_
subset S .snd = injective→is-embedding! (!-inj S)

El : V ℓ → Type ℓ
El V = ⌞ V ⌟

abstract
  El-is-set : (x : V ℓ) → is-set ⌞ x ⌟
  El-is-set x = embedding→is-hlevel 1 (subset x .snd) (hlevel 2)

instance
  hlevel-projection-v-label : hlevel-projection (quote v-label)
  hlevel-projection-v-label .has-level    = quote El-is-set
  hlevel-projection-v-label .get-level _  = pure (lit (nat 2))
  hlevel-projection-v-label .get-argument a with a
  ... | v-label-args x = pure x
  ... | _              = typeError []

private
  _ : {x : V ℓ} → is-set ⌞ x ⌟
  _ = hlevel 2

∅ⱽ : V ℓ
∅ⱽ = supv (Lift _ ⊥) ((λ ()) , (λ { _ (() , _) }))

one : V ℓ → V ℓ
one v = mkv λ where
  .Elt → Lift _ ⊤
  .idx _ → v
  .inj _ → refl

one-inj : {x y : V ℓ} → one x ≡ one y → x ≡ y
one-inj x = ap-set (ap₂ (λ e y → (e ! y) .tree) x (to-pathp refl))

two : (x y : V ℓ) → x ≠ y → V ℓ
two  x y d = mkv λ where
  .Elt → Lift _ Bool
  .idx (lift true)  → x
  .idx (lift false) → y

  .inj {lift true}  {lift true}  p → refl
  .inj {lift true}  {lift false} p → absurd (d p)
  .inj {lift false} {lift true}  p → absurd (d (sym p))
  .inj {lift false} {lift false} p → refl

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

x≠[x] : (x : V ℓ) → x ≡ one x → ⊥
x≠[x] x p = ∈-irrefl x (subst (x ∈_) (sym p) (lift tt , refl))

lookup→member : (S : V ℓ) {x : V ℓ} {j : ⌞ S ⌟} → (S ! j) ≡ x → x ∈ S
lookup→member S p with S .tree | S .uniq
... | sup x f | _ = _ , ap tree p

open import Data.Sum

sucv : V ℓ → V ℓ
sucv x = mkv λ where
  .Elt → ⊤ ⊎ El x

  .idx (inl tt) → x
  .idx (inr j)  → subset x .fst j

  .inj {inl _} {inl _} p → refl
  .inj {inl _} {inr _} p → absurd (∈-irrefl x (lookup→member x (sym p)))
  .inj {inr _} {inl _} p → absurd (∈-irrefl x (lookup→member x p))
  .inj {inr _} {inr _} p → ap inr (ap fst (subset x .snd _ (_ , p) (_ , refl)))

Natⱽ : V lzero
Natⱽ = mkv (mkV.constructor _ encoden encoden-inj) where
  encoden : Nat → V ℓ
  encoden zero    = ∅ⱽ
  encoden (suc x) = sucv (encoden x)

  encoden-inj : ∀ {ℓ} → injective (encoden {ℓ})
  encoden-inj {ℓ} p = Fin-injective (Equiv.inverse (lemma _) ∙e path→equiv (ap El p) ∙e lemma _) where
    lemma : ∀ n → El (encoden {ℓ} n) ≃ Fin n
    lemma zero    = (λ ()) , record { is-eqv = λ x → absurd (Fin-absurd x) }
    lemma (suc n) = ⊎-ap id≃ (lemma n) ∙e Equiv.inverse Finite-successor

two-inj
  : {x₀ x₁ y₀ y₁ : V ℓ} {p : x₀ ≠ y₀} {q : x₁ ≠ y₁} (r : x₁ ≠ y₀)
  → two x₀ y₀ p ≡ two x₁ y₁ q
  → (x₀ ≡ x₁) × (y₀ ≡ y₁)
two-inj {x₀ = x₀} {x₁} {y₀} {y₁} {d₀} {d₁} ah α = done where
  p : Lift _ Bool ≡ Lift _ Bool
  p = ap El α

  q : {a b : Lift _ Bool} → transport p a ≡ b
    → subtree (two x₀ y₀ d₀ .tree) a ≡ subtree (two x₁ y₁ d₁ .tree) b
  q a i = v-subtree (α i .tree) (to-pathp {A = λ i → p i} a i)

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

abstract
  one≠∅ : {x : V ℓ} → one x ≠ ∅ⱽ
  one≠∅ p = subst ⌞_⌟ (ap El p) (lift tt) .lower

  one≠two : ∀ {x y z : V ℓ} {p} → one x ≠ two y z p
  one≠two p = true≠false (ap lower (subst is-prop (ap El p) (hlevel 1) _ _))

pair : V ℓ → V ℓ → V ℓ
pair a b =
  two
    (two (one a) ∅ⱽ one≠∅)
    (one (one b))
  (one≠two ∘ sym)

abstract
  pair-inj : {x x' y y' : V ℓ} → pair x y ≡ pair x' y' → Path (V ℓ × V ℓ) (x , y) (x' , y')
  pair-inj α =
    let
      (p1 , p2) = two-inj (one≠two ∘ sym) α
      (p1' , _) = two-inj one≠∅ p1
    in one-inj p1' ,ₚ one-inj (one-inj p2)

Σⱽ : (X : V ℓ) (Y : El X → V ℓ) → V ℓ
Σⱽ x y = mkv λ where
  .Elt         → Σ[ i ∈ x ] El (y i)
  .idx (a , b) → pair (x ! a) (y a ! b)

  .inj {a , b} {a' , b'} α →
    let
      p1 , p2 = Σ-pathp.from (pair-inj α)

      p : a ≡ a'
      p = !-inj x p1

      aum = subst₂ (λ e b' → (y a ! b) ≡ (y e ! b')) (sym p) (to-pathp refl) p2
    in Σ-pathp (!-inj x p1) (to-pathp⁻ (!-inj (y a) aum))

module _ {A : Type ℓ} {B : A → Type ℓ} where
  is-functional : (Σ[ a ∈ A ] B a → Ω) → Ω
  is-functional R = elΩ ((a : A) → is-contr (Σ[ b ∈ B a ] ((a , b) ∈ R)))

  graph
    : (∀ x → is-set (B x))
    → (∀ x → B x)
    → ∫ₚ is-functional
  graph bset f = (λ (x , y) → elΩ (f x ≡ y)) , inc (λ a → contr (f a , inc refl) (elim! λ y p → Σ-prop-path! p))
    where instance
      _ : ∀ {x} → H-Level (B x) 2
      _ = hlevel-instance (bset _)

  graph-inj
    : (p : ∀ x → is-set (B x)) (f g : (x : A) → B x)
    → graph p f ≡ graph p g → f ≡ g
  graph-inj bset f g α = funext λ a → case subst (λ e → (a , f a) ∈ e) (ap fst α) (inc refl) of sym
    where instance
      _ : ∀ {x} → H-Level (B x) 2
      _ = hlevel-instance (bset _)

subsetⱽ : (x : V ℓ) → (El x → Ω) → V ℓ
subsetⱽ v f = mkv λ where
  .Elt         → Σ[ i ∈ v ] (i ∈ f)
  .idx (x , _) → v ! x
  .inj α       → Σ-prop-path! (!-inj v α)

subsetⱽ-inj : (x : V ℓ) (p q : El x → Ω) → subsetⱽ x p ≡ subsetⱽ x q → p ≡ q
subsetⱽ-inj x p q α = funext λ ex →
  let
    hum : ∀ {a b} (p : PathP (λ i → El (α i)) a b) → a .fst ≡ b .fst
    hum p = !-inj x (ap-set (λ i → (α i ! p i) .tree))
  in Ω-ua
    (λ a →
      let (ix , pix) = subst El α (ex , a)
       in subst (_∈ q) (sym (hum {ex , a} {ix , pix} (to-pathp refl))) pix)
    (λ a →
      let (ix , pix) = subst El (sym α) (ex , a)
       in subst (_∈ p) (hum {ix , pix} {ex , a} (to-pathp⁻ refl)) pix)

ℙⱽ : V ℓ → V ℓ
ℙⱽ x = mkv λ where
  .Elt           → El x → Ω
  .idx p         → subsetⱽ x p
  .inj {p} {q} α → subsetⱽ-inj _ _ _ α

realignⱽ : (x : V ℓ) {T : Type ℓ} (e : T → El x) → injective e → V ℓ
{-# INLINE realignⱽ #-}
realignⱽ x {T} f α = mkv λ where
  .Elt   → T
  .idx i → x ! f i
  .inj i → α (!-inj x i)

Πⱽ : (A : V ℓ) (B : El A → V ℓ) → V ℓ
Πⱽ A B = realignⱽ
  (subsetⱽ (ℙⱽ (Σⱽ A B)) is-functional)
  (graph λ x → El-is-set (B x))
  (graph-inj _ _ _)

Lift-inj : ∀ {ℓ} ℓ' → is-embedding {A = Type ℓ} (Lift ℓ')
Lift-inj ℓ' = cancellable→embedding λ {x} {y} →
  Lift ℓ' x ≡ Lift ℓ' y ≃⟨ _ , univalence ⟩
  Lift ℓ' x ≃ Lift ℓ' y ≃⟨ ≃-ap Lift-≃ Lift-≃ ⟩
  x ≃ y                 ≃⟨ _ , univalence⁻¹ ⟩
  x ≡ y                 ≃∎

raise : ∀ ℓ' → V ℓ → V (ℓ ⊔ ℓ')
raise {ℓ = ℓ} ℓ' = wrap module raise where
  raise' : V' ℓ → V' (ℓ ⊔ ℓ')
  raise' (sup x f) = sup (Lift ℓ' x) (λ (lift i) → raise' (f i))

  module l {x} {y} = Equiv (ap (Lift {ℓ} ℓ') {x} {y} , embedding→cancellable (Lift-inj ℓ'))

  abstract
    inj' : (x y : V' ℓ) → (raise' x ≡ raise' y) ≃ (x ≡ y)
    inj' (sup x f) (sup y g) =
      raise' (sup x f) ≡ raise' (sup y g)
        ≃⟨ ap-equiv W-fixpoint ⟩
      (Lift ℓ' x , raise' ∘ f ∘ lower) ≡ (Lift ℓ' y , raise' ∘ g ∘ lower)
        ≃˘⟨ Σ-pathp≃ ⟩
      (Σ (Lift ℓ' x ≡ Lift ℓ' y) (λ p → PathP (λ i → p i → V' (ℓ ⊔ ℓ')) (raise' ∘ f ∘ lower) (raise' ∘ g ∘ lower)))
        ≃˘⟨ Σ-ap-fst (Equiv.inverse l.inverse) ⟩
      (Σ (x ≡ y) λ p → PathP (λ i → Lift ℓ' (p i) → V' (ℓ ⊔ ℓ')) (raise' ∘ f ∘ lower) (raise' ∘ g ∘ lower))
        ≃⟨ Σ-ap-snd (λ p → (λ p i x → p i (lift x)) , is-iso→is-equiv (iso _ (λ x → refl) λ x → refl)) ⟩
      (Σ (x ≡ y) λ p → PathP (λ i → p i → V' (ℓ ⊔ ℓ')) (raise' ∘ f) (raise' ∘ g))
        ≃⟨ Σ-ap-snd
            (λ p → J (λ y p → {g : y → V' ℓ} → PathP (λ i → p i → V' (ℓ ⊔ ℓ')) (raise' ∘ f) (raise' ∘ g) ≃ PathP (λ i → p i → V' ℓ) f g)
              (Equiv.inverse funext≃ ∙e Π-ap-cod (λ x → inj' (f x) _) ∙e funext≃)
            p)
          ⟩
      (Σ (x ≡ y) λ p → PathP (λ i → p i → V' ℓ) f g)
        ≃⟨ Σ-pathp≃ ⟩
      (x , f) ≡ (y , g)
        ≃˘⟨ ap-equiv W-fixpoint ⟩
      sup x f ≡ sup y g
        ≃∎

  emb : is-embedding raise'
  emb = cancellable→embedding (inj' _ _)

  go : (w : V' ℓ) (u : is-iterative-embedding w) → V (ℓ ⊔ ℓ')
  goβ : (w : V' ℓ) (u : is-iterative-embedding w) → go w u .tree ≡ raise' w

  go (sup x f) (φ , r) .tree = raise' (sup x f)
  go (sup x f) (φ , r) .uniq =
    ∘-is-embedding (∘-is-embedding emb φ) (is-equiv→is-embedding (Lift-≃ .snd))
    , λ (lift y) → let it = go (f y) (r y) .uniq in subst is-iterative-embedding (goβ (f y) (r y)) it

  goβ (sup x f) (_ , _) = refl

  wrap : V ℓ → V (ℓ ⊔ ℓ')
  wrap S = go (S .tree) (S .uniq)

  is-inj : injective wrap
  is-inj α = ap-set (ap fst (emb _ (_ , sym (goβ _ _) ∙ ap tree α ∙ goβ _ _) (_ , refl)))

  ungo : (w : V' ℓ) (u : is-iterative-embedding w) → v-label (go w u .tree) ≃ v-label w
  ungo (sup x f) u .fst = lower
  ungo (sup x f) u .snd = is-iso→is-equiv (iso lift (λ _ → refl) λ _ → refl)

  unraise : ∀ x → El (wrap x) ≃ El x
  unraise x = ungo (x .tree) (x .uniq)

  module unraise x = Equiv (unraise x)

Vⱽ : ∀ {ℓ} → V (lsuc ℓ)
Vⱽ {ℓ} = mkv λ where
  .Elt → V ℓ
  .idx → raise _
  .inj → raise.is-inj _
```
