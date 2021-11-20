```
open import 1Lab.Path.Groupoid
open import 1Lab.Univalence
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.HLevel.Retracts where

open isContr public
```

# Closure of h-levels

<!--
```
private variable
  ℓ : Level
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

```
isContr-retract : (f : A → B) (g : B → A)
                → isLeftInverse f g
                → isContr A
                → isContr B
centre (isContr-retract f g h isC) = f (isC .centre)
paths (isContr-retract f g h isC) x =
  f (isC .centre) ≡⟨ ap f (isC .paths _) ⟩
  f (g x)         ≡⟨ h _ ⟩
  x               ∎
```

We must also show that retracts of _propositions_ are propositions:

```
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

```
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

```
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
      sym (h x) ∙ ap f (ap g path) ∙ h y ∙ refl ≡⟨ ap (λ e → sym (h _) ∙ _ ∙ e) (∙-id-right (h _)) ⟩
      sym (h x) ∙ ap f (ap g path) ∙ h y        ≡⟨ ap₂ _∙_ refl (sym (homotopy-natural h _)) ⟩
      sym (h x) ∙ h x ∙ path                    ≡⟨ ∙-assoc _ _ _ ⟩
      (sym (h x) ∙ h x) ∙ path                  ≡⟨ ap₂ _∙_ (∙-inv-l (h x)) refl ⟩
      refl ∙ path                               ≡⟨ ∙-id-left path ⟩
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

```
isHLevel-iso : (n : Nat) (f : A → B) → isIso f → isHLevel A n → isHLevel B n
isHLevel-iso n f is-iso =
  isHLevel-retract n f (is-iso .isIso.g)
                       (is-iso .isIso.right-inverse)

isHLevel-equiv : (n : Nat) (f : A → B) → isEquiv f → isHLevel A n → isHLevel B n
isHLevel-equiv n f eqv = isHLevel-iso n f (isEquiv→isIso eqv)
```

# Functions into n-types

Since h-levels are closed under retracts, The type of functions into a
homotopy n-type is itself a homotopy n-type.

```
isHLevelΠ : {a b : _} {A : Type a} {B : A → Type b}
          → (n : Nat) (Bhl : (x : A) → isHLevel (B x) n)
          → isHLevel ((x : A) → B x) n
isHLevelΠ 0 bhl = contr (λ x → bhl _ .centre) λ x i a → bhl _ .paths (x a) i
isHLevelΠ 1 bhl f g i a = bhl a (f a) (g a) i
isHLevelΠ (suc (suc n)) bhl f g =
  isHLevel-retract (suc n) funext happly (λ x → refl)
    (isHLevelΠ (suc n) λ x → bhl x (f x) (g x))
```

