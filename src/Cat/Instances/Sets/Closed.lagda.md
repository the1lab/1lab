<!--
```agda
open import Cat.Instances.Sets.Complete
open import Cat.Diagram.Exponential
open import Cat.Prelude
```
-->

```agda
module Cat.Instances.Sets.Closed where
```

<!--
```agda
open is-exponential
open Exponential
private variable
  ℓ : Level
```
-->

# Sets is cartesian closed {defines="sets-is-cartesian-closed"}

The category of [[sets]] is the archetypal [[cartesian closed category]]:
the [[exponential object]] $B^A$ between two sets is simply the set of
functions $A \to B$, with the evaluation map being honest-to-goodness
function application. The $\beta$ and $\eta$ laws hold definitionally.

```agda
Sets-exponentials : (A B : Set ℓ) → Exponential (Sets ℓ) Sets-cartesian A B
Sets-exponentials A B .B^A = el! (∣ A ∣ → ∣ B ∣)
Sets-exponentials A B .ev (f , x) = f x
Sets-exponentials A B .has-is-exp .ƛ m γ a = m (γ , a)
Sets-exponentials A B .has-is-exp .commutes m = refl
Sets-exponentials A B .has-is-exp .unique m' p i γ a = p i (γ , a)
```

Since exponentials exist for every pair of sets, the category of sets is
cartesian closed.

```agda
Sets-closed : Cartesian-closed (Sets ℓ) Sets-cartesian
Sets-closed .Cartesian-closed.has-exp = Sets-exponentials
```

This is the base case of the "mapping space" story in geometry: in any
category of [[sheaves]] the [[exponentials of sheaves|exponential]]
$\rm{Maps}(X, F)$ is computed by the same universal property, with sets
of functions replaced by sets of *plots* $U \times X \to F$.
