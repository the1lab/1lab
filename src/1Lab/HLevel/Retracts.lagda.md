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
retract→is-contr : (f : A → B) (g : B → A)
                → is-left-inverse f g
                → is-contr A
                → is-contr B
retract→is-contr f g h isC .centre = f (isC .centre)
retract→is-contr f g h isC .paths x =
  f (isC .centre) ≡⟨ ap f (isC .paths _) ⟩
  f (g x)         ≡⟨ h _ ⟩
  x               ∎
```

We must also show that retracts of _propositions_ are propositions:

```agda
retract→is-prop : (f : A → B) (g : B → A)
               → is-left-inverse f g
               → is-prop A
               → is-prop B
retract→is-prop f g h propA x y =
  x       ≡⟨ sym (h _) ⟩
  f (g x) ≡⟨ ap f (propA _ _) ⟩
  f (g y) ≡⟨ h _ ⟩
  y       ∎
```

Now we can extend this to all h-levels by induction:

```agda
retract→is-hlevel : (n : Nat) (f : A → B) (g : B → A)
                 → is-left-inverse f g
                 → is-hlevel A n
                 → is-hlevel B n
retract→is-hlevel 0 = retract→is-contr
retract→is-hlevel 1 = retract→is-prop
```

For the base case, we already have the proofs we're after. For the
inductive case, a function `g x ≡ g y → x ≡ y` is constructed, which is
a left inverse to the function `ap g`. Then, since `(g x) ≡ (g y)` is a
homotopy (n+1)-type, we conclude that so is `x ≡ y`.

```agda
retract→is-hlevel (suc (suc n)) f g h hlevel x y =
  retract→is-hlevel (suc n) sect (ap g) inv (hlevel (g x) (g y))
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
    inv : is-left-inverse sect (ap g)
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
iso→is-hlevel : (n : Nat) (f : A → B) → is-iso f → is-hlevel A n → is-hlevel B n
iso→is-hlevel n f is-iso =
  retract→is-hlevel n f (is-iso .is-iso.inv)
                       (is-iso .is-iso.rinv)

equiv→is-hlevel : (n : Nat) (f : A → B) → is-equiv f → is-hlevel A n → is-hlevel B n
equiv→is-hlevel n f eqv = iso→is-hlevel n f (is-equiv→is-iso eqv)

is-hlevel≃ : (n : Nat) → (A ≃ B) → is-hlevel A n → is-hlevel B n
is-hlevel≃ n (f , eqv) = iso→is-hlevel n f (is-equiv→is-iso eqv)
```

## Functions into n-types

Since h-levels are closed under retracts, The type of functions into a
homotopy n-type is itself a homotopy n-type.

```agda
Π-is-hlevel : ∀ {a b} {A : Type a} {B : A → Type b}
          → (n : Nat) (Bhl : (x : A) → is-hlevel (B x) n)
          → is-hlevel ((x : A) → B x) n
Π-is-hlevel 0 bhl = contr (λ x → bhl _ .centre) λ x i a → bhl _ .paths (x a) i
Π-is-hlevel 1 bhl f g i a = bhl a (f a) (g a) i
Π-is-hlevel (suc (suc n)) bhl f g =
  retract→is-hlevel (suc n) funext happly (λ x → refl)
    (Π-is-hlevel (suc n) λ x → bhl x (f x) (g x))
```

By taking `B` to be a type rather than a family, we get that `A → B`
also inherits the h-level of B.

```agda
fun-is-hlevel : ∀ {a b} {A : Type a} {B : Type b}
          → (n : Nat) → is-hlevel B n
          → is-hlevel (A → B) n
fun-is-hlevel n hl = Π-is-hlevel n (λ _ → hl)
```

## Sums of n-types

A similar argument, using the fact that [paths of pairs are pairs of
paths], shows that dependent sums are also closed under h-levels.

[paths of pairs are pairs of paths]: agda://1Lab.Type.Sigma#Σ-path-iso

```agda
Σ-is-hlevel : {A : Type ℓ} {B : A → Type ℓ'} (n : Nat)
            → is-hlevel A n
            → ((x : A) → is-hlevel (B x) n)
            → is-hlevel (Σ B) n
Σ-is-hlevel 0 acontr bcontr =
  contr (acontr .centre , bcontr _ .centre)
    λ x → Σ-path-p (acontr .paths _)
                  (is-prop→PathP (λ _ → is-contr→is-prop (bcontr _)) _ _)

Σ-is-hlevel 1 aprop bprop (a , b) (a' , b') i =
  (aprop a a' i) , (is-prop→PathP (λ i → bprop (aprop a a' i)) b b' i)

Σ-is-hlevel {B = B} (suc (suc n)) h1 h2 x y =
  iso→is-hlevel (suc n)
    (is-iso.inverse (Σ-path-iso .snd) .is-iso.inv)
    (Σ-path-iso .snd)
    (Σ-is-hlevel (suc n) (h1 (fst x) (fst y)) λ x → h2 _ _ _)
```

Similarly for dependent products and functions, there is a non-dependent
version of `Σ-is-hlevel`{.Agda} that expresses closure of h-levels under
`_×_`{.Agda}.

```agda
×-is-hlevel : ∀ {a b} {A : Type a} {B : Type b}
          → (n : Nat)
          → is-hlevel A n → is-hlevel B n
          → is-hlevel (A × B) n
×-is-hlevel n ahl bhl = Σ-is-hlevel n ahl (λ _ → bhl)
```

Similarly, `Lift`{.Agda} does not induce a change of h-levels, i.e. if
$A$ is an $n$-type in a universe $U$, then it's also an $n$-type in any
successor universe:

```agda
Lift-is-hlevel : ∀ {a b} {A : Type a}
              → (n : Nat)
              → is-hlevel A n
              → is-hlevel (Lift b A) n
Lift-is-hlevel n a-hl = retract→is-hlevel n lift Lift.lower (λ _ → refl) a-hl
```
