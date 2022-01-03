```agda
open import 1Lab.Path.Groupoid
open import 1Lab.Type.Sigma
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.HLevel.Retracts where
```

# Closure of h-levels

<!--
```
private variable
  ℓ ℓ' : Level
  A B C : Type ℓ
  F G : A → Type ℓ
```
-->

The homotopy n-types have many closure properties. A trivial example is
that they are closed under equivalences, since any property of types is
preserved by equivalence (This is the [univalence axiom]). More
interesting is that they are closed under retractions:

[univalence axiom]: 1Lab.Univalence.html#the-axiom

## Retractions

The first base case is to show that **retracts** of contractible types
are contractible. We say that $A$ is a retract of $B$ if there is a map
$f : A \to B$ admitting a `right-inverse`{.Agda}. This means that $f$ is
the retraction (the left inverse). The proof is a calculation:

```agda
isContr-retract : (f : A → B) (g : B → A)
                → isLeftInverse f g
                → isContr A
                → isContr B
isContr-retract f g h isC .centre = f (isC .centre)
isContr-retract f g h isC .paths x =
  f (isC .centre) ≡⟨ ap f (isC .paths _) ⟩
  f (g x)         ≡⟨ h _ ⟩
  x               ∎
```

We must also show that retracts of _propositions_ are propositions:

```agda
isProp-retract : (f : A → B) (g : B → A)
               → isLeftInverse f g
               → isProp A
               → isProp B
isProp-retract f g h propA x y =
  x       ≡⟨ sym (h _) ⟩
  f (g x) ≡⟨ ap f (propA _ _) ⟩
  f (g y) ≡⟨ h _ ⟩
  y       ∎
```

Now we can extend this to all h-levels by induction:

```agda
isHLevel-retract : (n : Nat) (f : A → B) (g : B → A)
                 → isLeftInverse f g
                 → isHLevel A n
                 → isHLevel B n
isHLevel-retract 0 = isContr-retract
isHLevel-retract 1 = isProp-retract
```

For the base case, we already have the proofs we're after. For the
inductive case, a function `g x ≡ g y → x ≡ y` is constructed, which is
a left inverse to the function `ap g`. Then, since `(g x) ≡ (g y)` is a
homotopy (n+1)-type, we conclude that so is `x ≡ y`.

```agda
isHLevel-retract (suc (suc n)) f g h hlevel x y =
  isHLevel-retract (suc n) sect (ap g) inv (hlevel (g x) (g y))
  where
    sect : g x ≡ g y → x ≡ y
    sect path =
      x       ≡⟨ sym (h _) ⟩
      f (g x) ≡⟨ ap f path ⟩
      f (g y) ≡⟨ h _ ⟩
      y       ∎
```

The left inverse is constructed out of `ap`{.Agda} and the given
homotopy.
  
```
    inv : isLeftInverse sect (ap g)
    inv path =
      sym (h x) ∙ ap f (ap g path) ∙ h y ∙ refl ≡⟨ ap (λ e → sym (h _) ∙ _ ∙ e) (∙-id-r (h _)) ⟩
      sym (h x) ∙ ap f (ap g path) ∙ h y        ≡⟨ ap₂ _∙_ refl (sym (homotopy-natural h _)) ⟩
      sym (h x) ∙ h x ∙ path                    ≡⟨ ∙-assoc _ _ _ ⟩
      (sym (h x) ∙ h x) ∙ path                  ≡⟨ ap₂ _∙_ (∙-inv-l (h x)) refl ⟩
      refl ∙ path                               ≡⟨ ∙-id-l path ⟩
      path                                      ∎
```

The proof that this function _does_ invert `ap g` on the left is boring,
but it consists mostly of symbol pushing. The only non-trivial step, and
the key to the proof, is the theorem that [homotopies are natural
transformations]: We can flip `ap f (ap g path)` and `h y` to get a pair
of paths that annihilates on the left, and `path` on the right.

[homotopies are natural transformations]: agda://1Lab.Path#homotopy-natural

### Equivalences

It follows, without a use of univalence, that h-levels are closed under
isomorphisms and equivalences:

```agda
isHLevel-iso : (n : Nat) (f : A → B) → isIso f → isHLevel A n → isHLevel B n
isHLevel-iso n f is-iso =
  isHLevel-retract n f (is-iso .isIso.inv)
                       (is-iso .isIso.rinv)

isHLevel-equiv : (n : Nat) (f : A → B) → isEquiv f → isHLevel A n → isHLevel B n
isHLevel-equiv n f eqv = isHLevel-iso n f (isEquiv→isIso eqv)

isHLevel≃ : (n : Nat) → (A ≃ B) → isHLevel A n → isHLevel B n
isHLevel≃ n (f , eqv) = isHLevel-iso n f (isEquiv→isIso eqv)
```

## Functions into n-types

Since h-levels are closed under retracts, The type of functions into a
homotopy n-type is itself a homotopy n-type.

```agda
isHLevelΠ : ∀ {a b} {A : Type a} {B : A → Type b}
          → (n : Nat) (Bhl : (x : A) → isHLevel (B x) n)
          → isHLevel ((x : A) → B x) n
isHLevelΠ 0 bhl = contr (λ x → bhl _ .centre) λ x i a → bhl _ .paths (x a) i
isHLevelΠ 1 bhl f g i a = bhl a (f a) (g a) i
isHLevelΠ (suc (suc n)) bhl f g =
  isHLevel-retract (suc n) funext happly (λ x → refl)
    (isHLevelΠ (suc n) λ x → bhl x (f x) (g x))
```

By taking `B` to be a type rather than a family, we get that `A → B`
also inherits the h-level of B.

```agda
isHLevel→ : ∀ {a b} {A : Type a} {B : Type b}
          → (n : Nat) → isHLevel B n
          → isHLevel (A → B) n
isHLevel→ n hl = isHLevelΠ n (λ _ → hl)
```

## Sums of n-types

A similar argument, using the fact that [paths of pairs are pairs of
paths], shows that dependent sums are also closed under h-levels.

[paths of pairs are pairs of paths]: agda://1Lab.Type.Sigma#Σ-Path-iso

```agda
isHLevelΣ : {A : Type ℓ} {B : A → Type ℓ'} (n : Nat)
            → isHLevel A n
            → ((x : A) → isHLevel (B x) n)
            → isHLevel (Σ B) n
isHLevelΣ 0 acontr bcontr =
  contr (acontr .centre , bcontr _ .centre)
    λ x → Σ-PathP (acontr .paths _)
                  (isProp→PathP (λ _ → isContr→isProp (bcontr _)) _ _)

isHLevelΣ 1 aprop bprop (a , b) (a' , b') i =
  (aprop a a' i) , (isProp→PathP (λ i → bprop (aprop a a' i)) b b' i)

isHLevelΣ {B = B} (suc (suc n)) h1 h2 x y =
  isHLevel-iso (suc n)
    (isIso.inverse (Σ-Path-iso .snd) .isIso.inv)
    (Σ-Path-iso .snd)
    (isHLevelΣ (suc n) (h1 (fst x) (fst y)) λ x → h2 _ _ _)
```

Similarly for dependent products and functions, there is a non-dependent
version of `isHLevelΣ`{.Agda} that expresses closure of h-levels under
`_×_`{.Agda}.

```agda
isHLevel× : ∀ {a b} {A : Type a} {B : Type b}
          → (n : Nat)
          → isHLevel A n → isHLevel B n
          → isHLevel (A × B) n
isHLevel× n ahl bhl = isHLevelΣ n ahl (λ _ → bhl)
```

Similarly, `Lift`{.Agda} does not induce a change of h-levels, i.e. if
$A$ is an $n$-type in a universe $U$, then it's also an $n$-type in any
successor universe:

```agda
isHLevel-Lift : ∀ {a b} {A : Type a}
              → (n : Nat)
              → isHLevel A n
              → isHLevel (Lift b A) n
isHLevel-Lift n a-hl = isHLevel-retract n lift Lift.lower (λ _ → refl) a-hl
```
