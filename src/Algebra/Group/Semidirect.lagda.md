<!--
```agda
open import Algebra.Group.Cat.FinitelyComplete
open import Algebra.Group.Cat.Base
open import Algebra.Group.Action
open import Algebra.Group

open import Cat.Prelude

open is-group-hom
open make-group
```
-->

```agda
module Algebra.Group.Semidirect {ℓ} where
```

# Semidirect products of groups {defines="semidirect-product"}

Given a [[group]] $A$ [[acting|group action]] on another group $B$ (that is,
equipped with a [[group homomorphism]] $\varphi : A \to \rm{Aut}(B)$ from $A$ to
the [[automorphism group]] of $B$), we define the **semidirect product**
$A \ltimes B$ as a variant of the [[direct product|direct product of groups]] $A \times B$ in which
the $A$ component influences the multiplication of the $B$ component.

To motivate the concept, let's consider some examples:

- The [[dihedral group]] of order $2n$, $D_n$, which is the group of
symmetries of a regular $n$-gon, can be defined as the semidirect product
$\ZZ/2\ZZ \ltimes \ZZ/n\ZZ$, where the action of $\ZZ/2\ZZ$ sends $1$
to the [[negation automorphism]] of $\ZZ/n\ZZ$. Intuitively, a symmetry
of the regular $n$-gon has two components: a reflection (captured by the
cyclic group $\ZZ/2\ZZ$) and a rotation (captured by the cyclic group $\ZZ/n\ZZ$);
but when combining two symmetries, a reflection will swap the direction
of further rotations. This is exactly captured by the semidirect product.
- The group of isometries of the square lattice $\ZZ^2$ (considered
as a subspace of $\RR^2$), which we will refer to by its IUC notation
$p4m$, consists of reflections, rotations and translations. It can thus
be defined as a further semidirect product of the [[dihedral group]]
$D_4$ acting on the group of translations $\ZZ^2$ in the obvious way.
- Leaving the discrete world, the group of all isometries of the plane
$\RR^2$ can be seen analogously as the semidirect product of the
orthogonal group $O(2)$ acting on the translation group $\RR^2$, where
$O(2)$ is itself the semidirect product of $\ZZ/2\ZZ$ acting on the
*special* orthogonal group $SO(2)$, also known as the circle group.

<!--
```agda
module _ (A : Group ℓ) (B : Group ℓ) (φ : Action (Groups ℓ) A B) where
  private
    module A = Group-on (A .snd)
    module B = Group-on (B .snd)
```
-->

We are now ready to define $A \ltimes B$. The underlying set is the
cartesian product $A \times B$; the unit is the pair of units
$(1_A, 1_B)$. The interesting part of the definition is the multiplication:
we set $(a, b) \star (a', b') = (a \star_A a', \varphi_{a'}(b) \star_B b')$.

::: note
Since our [[group actions]] are *right* actions, what we define here
is the *right* semidirect product. The version that works with *left*
actions instead would be $(a \star_A a', b \star_B \varphi_{a}(b'))$.
:::

```agda
  Semidirect-product : Group ℓ
  Semidirect-product = to-group A⋉B where
    A⋉B : make-group (⌞ A ⌟ × ⌞ B ⌟)
    A⋉B .group-is-set = hlevel 2
    A⋉B .unit = A.unit , B.unit
    A⋉B .mul (a , b) (a' , b') = a A.⋆ a' , (φ # a' # b) B.⋆ b'
```

The definition of the inverses is then forced, and we easily check that
the group axioms are verified.

```agda
    A⋉B .inv (a , b) = a A.⁻¹ , (φ # (a A.⁻¹) # b) B.⁻¹
    A⋉B .assoc (ax , bx) (ay , by) (az , bz) = Σ-pathp A.associative $
      ⌜ φ # (ay A.⋆ az) # bx ⌝ B.⋆ φ # az # by B.⋆ bz ≡⟨ ap! (unext (φ .preserves .pres-⋆ _ _) _) ⟩
      φ # az # (φ # ay # bx) B.⋆ φ # az # by B.⋆ bz   ≡⟨ B.associative ⟩
      (φ # az # (φ # ay # bx) B.⋆ φ # az # by) B.⋆ bz ≡˘⟨ ap (B._⋆ bz) ((φ # az) .Groups.to .preserves .pres-⋆ _ _) ⟩
      φ # az # (φ # ay # bx B.⋆ by) B.⋆ bz            ∎
    A⋉B .invl (a , b) = Σ-pathp A.inversel $
      φ # a # ⌜ (φ # (a A.⁻¹) # b) B.⁻¹ ⌝ B.⋆ b ≡˘⟨ ap¡ (pres-inv ((φ # _) .Groups.to .preserves)) ⟩
      φ # a # (φ # (a A.⁻¹) # (b B.⁻¹)) B.⋆ b   ≡˘⟨ ap (B._⋆ b) (unext (pres-⋆ (φ .preserves) _ _) _) ⟩
      φ # ⌜ a A.⁻¹ A.⋆ a ⌝ # (b B.⁻¹) B.⋆ b     ≡⟨ ap! A.inversel ⟩
      φ # A.unit # (b B.⁻¹) B.⋆ b               ≡⟨ ap (B._⋆ b) (unext (pres-id (φ .preserves)) _) ⟩
      b B.⁻¹ B.⋆ b                              ≡⟨ B.inversel ⟩
      B.unit                                    ∎
    A⋉B .idl (a , b) = Σ-pathp A.idl $
      φ # a # B.unit B.⋆ b ≡⟨ ap (B._⋆ b) (pres-id ((φ # a) .Groups.to .preserves)) ⟩
      B.unit B.⋆ b         ≡⟨ B.idl ⟩
      b                    ∎
```

The natural projection from $A \ltimes B$ to the first component $A$ is
a [[group homomorphism]], but the same cannot be said about the second
component (can you see why?).

```agda
  ⋉-proj : Groups.Hom Semidirect-product A
  ⋉-proj .hom = fst
  ⋉-proj .preserves .pres-⋆ _ _ = refl
```

When the action of $A$ on $B$ is [[trivial|trivial action]], i.e. $\varphi_a$ is the
identity automorphism for all $a : A$, it's easy to see that the
semidirect product $A \ltimes B$ agrees with the direct product
$A \times B$.

<!--
```agda
module _ (A : Group ℓ) (B : Group ℓ) where
  private
    module A = Group-on (A .snd)
    module B = Group-on (B .snd)
```
-->

```agda
  Semidirect-trivial
    : Semidirect-product A B (trivial-action A B) ≡ Direct-product A B
  Semidirect-trivial = ∫-Path
    (total-hom (λ x → x) (record { pres-⋆ = λ _ _ → refl }))
    id-equiv
```

Another way to understand the semidirect product is to look at its
definition [[for concrete groups|semidirect product of concrete groups]],
which is remarkably simple.
