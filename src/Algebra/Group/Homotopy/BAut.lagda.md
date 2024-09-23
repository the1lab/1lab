<!--
```agda
open import 1Lab.Prelude
```
-->

```agda
module Algebra.Group.Homotopy.BAut where
```

# Deloopings of automorphism groups

Recall that any set $X$ generates a group [[$\rm{Sym}(X)$|symmetric group]] given
by the automorphisms $X \simeq X$. We also have a generic construction
of [[deloopings]]: special spaces $K(G,1)$ (for a group $G$), where the
[[fundamental group]] $\pi_1(K(G,1))$ recovers $G$. For the specific case
of deloping automorphism groups, we can give an alternative
construction: The type of small types [[merely]] equivalent to $X$ has a
fundamental group of $\rm{Sym}(X)$.

```agda
module _ {ℓ} (T : Type ℓ) where
  BAut : Type (lsuc ℓ)
  BAut = Σ[ B ∈ Type ℓ ] ∥ T ≃ B ∥

  base : BAut
  base = T , inc (id , id-equiv)
```

The first thing we note is that `BAut`{.Agda} is a _[[connected]]_ type,
meaning that it only has "a single point", or, more precisely, that all
of its interesting information is in its (higher) path spaces:

```agda
  connected : (x : BAut) → ∥ x ≡ base ∥
  connected = elim! λ b e → inc (p b e) where
    p : ∀ b e → (b , inc e) ≡ base
    p _ = EquivJ (λ B e → (B , inc e) ≡ base) refl
```

We now turn to proving that $\pi_1(\baut(X)) \simeq (X \simeq X)$. We
will define a type family $\rm{Code}(b)$, where a value $p : \rm{Code}(x)$
codes for an identification $p \equiv \rm{base}$. Correspondingly, there
are functions to and from these types: The core of the proof is showing
that these functions, `encode`{.Agda} and `decode`{.Agda}, are inverses.

```agda
  Code : BAut → Type ℓ
  Code b = T ≃ b .fst

  encode : ∀ b → base ≡ b → Code b
  encode x p = path→equiv (ap fst p)

  decode : ∀ b → Code b → base ≡ b
  decode (b , eqv) rot = Σ-pathp (ua rot) (is-prop→pathp (λ _ → squash) _ _)
```

Recall that $\rm{base}$ is the type $T$ itself, equipped with the
identity equivalence. Hence, to code for an identification $\rm{base}
\equiv (X, e)$, it suffices to record $e$ --- which by univalence
corresponds to a path $\rm{ua}(e) : T \equiv X$.  We can not directly
extract the equivalence from a given point $(X, e) : \baut(X)$: it is
"hidden away" under a truncation. But, given an identification $p : b
\equiv \rm{base}$, we can recover the equivalence by seeing _how_ $p$
identifies $X \equiv T$.

```agda
  decode∘encode : ∀ b (p : base ≡ b) → decode b (encode b p) ≡ p
  decode∘encode b =
    J (λ b p → decode b (encode b p) ≡ p)
      (Σ-prop-square (λ _ → squash) sq)
    where
      sq : ua (encode base refl) ≡ refl
      sq = ap ua path→equiv-refl ∙ ua-id-equiv
```

`Encode`{.Agda ident=encode} and `decode`{.Agda} are inverses by a
direct application of `univalence`{.Agda}.

```agda
  encode∘decode : ∀ b (p : Code b) → encode b (decode b p) ≡ p
  encode∘decode b p = ua.η _
```

We now have the core result: Specialising `encode`{.Agda} and
`decode`{.Agda} to the `basepoint`{.Agda}, we conclude that loop space
$\rm{base} \equiv \rm{base}$ is equivalent to $\rm{Sym}(X)$.

```agda
  Ω¹BAut : (base ≡ base) ≃ (T ≃ T)
  Ω¹BAut = Iso→Equiv
    (encode base , iso (decode base) (encode∘decode base) (decode∘encode base))
```

We can also characterise the h-level of these connected components.
Intuitively the h-level should be one more than that of the type we're
delooping, because `BAut`{.Agda} "only has one point" (it's connected),
and as we established right above, the space of loops of that point is
the automorphism group we delooped. The trouble here is that
`BAut`{.Agda} has many points, and while we can pick paths between any
two of them, we can not do so _continuously_ (otherwise `BAut`{.Agda}
would be a proposition).

This turns out not to matter! Since "being of h-level $n$" is a
proposition, our discontinuous (i.e.: truncated) method of picking paths
is just excellent. In the case when $T$ is contractible, we can directly
get at the underlying equivalences, but for the higher h-levels, we
proceed exactly by using connectedness.

```agda
  BAut-is-hlevel : ∀ n → is-hlevel T n → is-hlevel BAut (1 + n)
  BAut-is-hlevel zero hl (x , f) (y , g) = Σ-prop-path! (sym (ua f') ∙ ua g')
    where
      extract : ∀ {X} → is-prop (T ≃ X)
      extract f g = ext λ x → ap fst $
        is-contr→is-prop ((f e⁻¹) .snd .is-eqv (hl .centre))
          (f .fst x , is-contr→is-prop hl _ _)
          (g .fst x , is-contr→is-prop hl _ _)

      f' = ∥-∥-rec extract (λ x → x) f
      g' = ∥-∥-rec extract (λ x → x) g
  BAut-is-hlevel (suc n) hl x y =
    ∥-∥-elim₂ {P = λ _ _ → is-hlevel (x ≡ y) (1 + n)}
      (λ _ _ → is-hlevel-is-prop _)
      (λ p q → transport (ap₂ (λ a b → is-hlevel (a ≡ b) (1 + n)) (sym p) (sym q))
        (Equiv→is-hlevel (1 + n) Ω¹BAut (≃-is-hlevel (1 + n) hl hl)))
      (connected x) (connected y)
```
