open import 1Lab.Reflection.Subst using (applyTC ; raiseTC)
open import 1Lab.Path.IdentitySystem
open import 1Lab.Reflection.HLevel
open import 1Lab.HLevel.Retracts
open import 1Lab.Reflection
open import 1Lab.Type.Sigma
open import 1Lab.Type.Pi
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

open import Data.Nat.Base

module 1Lab.Extensionality where

record Extensional {ℓ} (A : Type ℓ) (ℓ-rel : Level) : Typeω where
  field
    Pathᵉ : A → A → Type ℓ-rel
    reflᵉ : ∀ x → Pathᵉ x x
    idsᵉ : is-identity-system Pathᵉ reflᵉ

open Extensional using (Pathᵉ ; reflᵉ ; idsᵉ) public

Extensional-default : ∀ {ℓ} {A : Type ℓ} → Extensional A ℓ
Extensional-default .Pathᵉ   = _≡_
Extensional-default .reflᵉ _ = refl
Extensional-default .idsᵉ    = Path-identity-system

record Extensionality {ℓ} (A : Type ℓ) : Type where
  field lemma : Name

find-extensionality : Term → TC Term
find-extensionality tm = do
  tm ← reduce =<< wait-for-type tm
  let search = def (quote Extensionality) [ argN tm ]
  debugPrint "tactic.extensionality" 10 ("find-extensionality goal:\n  " ∷ termErr search ∷ [])

  runSpeculative do
    (mv , _) ← new-meta' search
    soln ← getInstances mv >>= λ where
      (x ∷ xs) → do
        it ← unquoteTC {A = Name} =<< normalise (def (quote Extensionality.lemma) (argN x ∷ []))
        debugPrint "tactic.extensionality" 10 (" ⇒ found lemma " ∷ termErr (def it []) ∷ [])
        pure (def it [])
      []       → do
        debugPrint "tactic.extensionality" 10 " ⇒ using default"
        pure (def (quote Extensional-default) [])

    pure (soln , false)

extensional : ∀ {ℓ} (A : Type ℓ) → Term → TC ⊤
extensional A goal = do
  `A ← quoteTC A
  candidate ← find-extensionality `A
  unify goal
    =<< checkType candidate (def (quote Extensional) [ argN `A , argN unknown ])

extensionalᶠ
  : ∀ {ℓ} {A : Type ℓ} → A → Term → TC ⊤
extensionalᶠ {A = A} fun goal = ⦇ wrap (quoteTC A) (quoteTC fun) ⦈ >>= id where
  work : Term → Term → TC Term
  work (pi dom@(arg ai _) (abs nm cod)) tm = do
    prf ← extendContext nm dom do
      tm ← raiseTC 1 tm
      tm ← applyTC tm (arg ai (var 0 []))
      work cod tm
    pure (lam (ai .ArgInfo.arg-vis) (abs nm prf))
  work _ tm = find-extensionality tm

  wrap : Term → Term → TC ⊤
  wrap t fn = do
    t ← wait-for-type t
    debugPrint "tactic.extensionality" 10 ("extensionalᶠ goal:\n  " ∷ termErr fn ∷ "\nof type\n  " ∷ termErr t ∷ [])
    prf ← work t fn
    unify goal prf

Extensional-Π
  : ∀ {ℓ ℓ' ℓr} {A : Type ℓ} {B : A → Type ℓ'}
  → {@(tactic extensionalᶠ B) sb : ∀ x → Extensional (B x) ℓr}
  → Extensional ((x : A) → B x) (ℓ ⊔ ℓr)
Extensional-Π {sb = sb} .Pathᵉ f g = ∀ x → Pathᵉ (sb _) (f x) (g x)
Extensional-Π {sb = sb} .reflᵉ f x = reflᵉ (sb x) (f x)
Extensional-Π {sb = sb} .idsᵉ .to-path h = funext λ i → sb i .idsᵉ .to-path (h i)
Extensional-Π {sb = sb} .idsᵉ .to-path-over h = funextP λ i → sb i .idsᵉ .to-path-over (h i)

Extensional-→
  : ∀ {ℓ ℓ' ℓr} {A : Type ℓ} {B : Type ℓ'}
  → {@(tactic extensional B) sb : Extensional B ℓr}
  → Extensional (A → B) (ℓ ⊔ ℓr)
Extensional-→ {sb = sb} = Extensional-Π {sb = λ _ → sb}

Extensional-×
  : ∀ {ℓ ℓ' ℓr ℓs} {A : Type ℓ} {B : Type ℓ'}
  → {@(tactic extensional A) sa : Extensional A ℓr}
  → {@(tactic extensional B) sb : Extensional B ℓs}
  → Extensional (A × B) (ℓr ⊔ ℓs)
Extensional-× {sa = sa} {sb = sb} .Pathᵉ (x , y) (x' , y') = Pathᵉ sa x x' × Pathᵉ sb y y'
Extensional-× {sa = sa} {sb = sb} .reflᵉ (x , y) = reflᵉ sa x , reflᵉ sb y
Extensional-× {sa = sa} {sb = sb} .idsᵉ .to-path (p , q) = ap₂ _,_
  (sa .idsᵉ .to-path p)
  (sb .idsᵉ .to-path q)
Extensional-× {sa = sa} {sb = sb} .idsᵉ .to-path-over (p , q) = Σ-pathp-dep
  (sa .idsᵉ .to-path-over p)
  (sb .idsᵉ .to-path-over q)

instance
  extensionality-fun : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
    → Extensionality (A → B)
  extensionality-fun = record { lemma = quote Extensional-→ }

  extensionality-Π : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
    → Extensionality ((x : A) → B x)
  extensionality-Π = record { lemma = quote Extensional-Π }

  extensionality-× : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
    → Extensionality (A × B)
  extensionality-× = record { lemma = quote Extensional-× }

ext
  : ∀ {ℓ ℓr} {A : Type ℓ} {@(tactic extensional A) r : Extensional A ℓr} {x y : A}
  → Pathᵉ r x y → x ≡ y
ext {r = r} p = r .idsᵉ .to-path p

trivial-worker
  : ∀ {ℓ ℓr} {A : Type ℓ}
  → (r : Extensional A ℓr)
  → (x y : A)
  → Term
  → TC ⊤
trivial-worker r x y goal = try where
  error : ∀ {ℓ} {A : Type ℓ} → TC A
  error = do
    `x ← quoteTC x
    `y ← quoteTC y
    typeError
      [ "trivialᵉ failed: the values\n  "
      , termErr `x
      , "\nand\n  "
      , termErr `y
      , "\nare not extensionally equal by refl."
      ]

  try : TC ⊤
  try = do
    `r ← wait-for-type =<< quoteωTC r
    ty ← quoteTC (Pathᵉ r x y)
    `x ← quoteTC x
    `refl ← checkType (def (quote reflᵉ) [ argN `r , argN `x ]) ty
      <|> error
    unify goal `refl

opaque
  trivialᵉ
    : ∀ {ℓ ℓr} {A : Type ℓ}
    → {@(tactic extensional A) r : Extensional A ℓr}
    → {x y : A}
    → {@(tactic trivial-worker r x y) p : Pathᵉ r x y}
    → x ≡ y
  trivialᵉ {r = r} {p = p} = r .idsᵉ .to-path p

Pathᵉ-is-hlevel
  : ∀ {ℓ ℓr} {A : Type ℓ} n (sa : Extensional A ℓr)
  → is-hlevel A (suc n)
  → ∀ {x y}
  → is-hlevel (Pathᵉ sa x y) n
Pathᵉ-is-hlevel n sa hl =
  is-hlevel≃ _ (identity-system-gives-path (sa .idsᵉ)) (Path-is-hlevel' _ hl _ _)

injection→extensional
  : ∀ {ℓ ℓ' ℓr} {A : Type ℓ} {B : Type ℓ'}
  → is-set B
  → (f : A → B)
  → (∀ {x y} → f x ≡ f y → x ≡ y)
  → Extensional B ℓr
  → Extensional A ℓr
injection→extensional b-set f inj ext .Pathᵉ x y = Pathᵉ ext (f x) (f y)
injection→extensional b-set f inj ext .reflᵉ x = reflᵉ ext (f x)
injection→extensional b-set f inj ext .idsᵉ =
  set-identity-system
    (λ x y → Pathᵉ-is-hlevel 1 ext b-set)
    (λ p → inj (ext .idsᵉ .to-path p))

injection→extensional!
  : ∀ {ℓ ℓ' ℓr} {A : Type ℓ} {B : Type ℓ'}
  → {@(tactic hlevel-tactic-worker) sb : is-set B}
  → {f : A → B}
  → (∀ {x y} → f x ≡ f y → x ≡ y)
  → Extensional B ℓr
  → Extensional A ℓr
injection→extensional! {sb = sb} {f} = injection→extensional sb f

private
  record Test : Type where
    no-eta-equality
    field
      foo     : Nat
      useless : is-equiv {A = Nat} id

  open Test

  t1 t2 : Test
  t1 .foo = 2
  t1 .useless = id-equiv

  t2 .foo = 2
  t2 .useless = id-equiv

  Extensional-Test : Extensional Test lzero
  Extensional-Test = injection→extensional! {sb = Nat-is-set} p Extensional-default where
    p : ∀ {x y} → x .foo ≡ y .foo → x ≡ y
    p r i .foo = r i
    p {x} {y} _ i .useless = is-equiv-is-prop id (x .useless) (y .useless) i

  instance
    _ : Extensionality Test
    _ = record { lemma = quote Extensional-Test }

  _ : t1 ≡ t2
  _ = trivialᵉ
