```agda
open import Cat.Instances.Elements
open import Cat.Instances.Functor
open import Cat.Diagram.Terminal
open import Cat.Instances.Sets
open import Cat.Functor.Base
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Reasoning

module Cat.Functor.Hom.Representable {o κ} {C : Precategory o κ} where
```

<!--
```agda
private
  module C = Cat.Reasoning C
  module C^ = Cat.Reasoning Cat[ C ^op , Sets κ ]
  module Sets = Cat.Reasoning (Sets κ)
open Element-hom
open Functor
open Element
open _=>_
```
-->

# Representable functors

A functor $F : \cC\op \to \Sets_\kappa$ (from a [locally
$\kappa$-small category][univ]) is said to be **representable** when it
is [naturally isomorphic][niso] to $\hom(-, X)$ for an object $X :
\cC$ (called the **representing object**) — that is, the functor $F$
classifies the _maps into_ $X$. Note that we can evidently dualise the
definition, to get what is called a **corepresentable functor**, one of
the form $\hom(X, -)$, but we refer informally to both of these
situations as "representables" and "representing objects".

[univ]: 1Lab.intro.html#universes-and-size-issues
[niso]: Cat.Instances.Functor.html#functor-categories

```agda
record Representation (F : Functor (C ^op) (Sets κ)) : Type (o ⊔ κ) where
  no-eta-equality
  field
    rep        : C.Ob
    represents : F C^.≅ よ₀ C rep

  equiv : ∀ {a} → C.Hom a rep ≃ ∣ F .F₀ a ∣
  equiv = Iso→Equiv λ where
    .fst                → represents .C^.from .η _
    .snd .is-iso.inv    → represents .C^.to .η _
    .snd .is-iso.rinv x → represents .C^.invr ηₚ _ $ₚ x
    .snd .is-iso.linv x → represents .C^.invl ηₚ _ $ₚ x

  module rep = C^._≅_ represents
  module Rep {a} = Equiv (equiv {a})

open Representation
open Representation using (module Rep) public
```

This definition is _deceptively_ simple: the idea of representable
functor (and of representing object) is _key_ to understanding the idea
of **universal property**, which could be called the most important
concept in category theory. Most constructions in category theory
specified in terms of the existence of certain maps are really instances
of representing objects for functors: [limits], [colimits], [coends],
[adjoint functors], [Kan extensions], etc.

[limits]: Cat.Diagram.Limit.Base.html
[coends]: Cat.Diagram.Coend.html
[colimits]: Cat.Diagram.Colimit.Base.html
[Kan extensions]: Cat.Functor.Kan.html
[adjoint functors]: Cat.Functor.Adjoint.html

The first thing we will observe is an immediate consequence of the
[Yoneda lemma]: representing objects are unique. Intuitively this is
because "$X$ is a representation of $F$" determines how $X$ reacts to
being mapped into, and since the only thing we can probe objects in an
arbitrary category by are morphisms, two objects which react to
morphisms in the same way must be isomorphic.

[Yoneda lemma]: Cat.Functor.Hom.html

```agda
representation-unique : {F : Functor (C ^op) (Sets κ)} (X Y : Representation F)
                      → X .rep C.≅ Y .rep
representation-unique X Y =
  is-ff→essentially-injective {F = よ C} (よ-is-fully-faithful C) よX≅よY where
    よX≅よY : よ₀ C (X .rep) C^.≅ よ₀ C (Y .rep)
    よX≅よY = (X .represents C^.Iso⁻¹) C^.∘Iso Y .represents
```

Therefore, if $\cC$ is a univalent category, then the type of
representations for a functor $F$ is a proposition. This does not follow
immediately from the lemma above: we also need to show that the
isomorphism computed by the full-faithfulness of the Yoneda embedding
commutes with the specified representation isomorphism.
This follows by construction, but the proof needs to commute

applications of functors and paths-from-isos, which is never pretty:

```agda
Representation-is-prop : ∀ {F} → is-category C → is-prop (Representation F)
Representation-is-prop {F = F} c-cat x y = path where
  module X = Representation x
  module Y = Representation y

  objs : X.rep ≡ Y.rep
  objs = c-cat .to-path (representation-unique x y)

  path : x ≡ y
  path i .rep = objs i
  path i .represents =
    C^.≅-pathp refl (ap (よ₀ C) objs) {f = X.represents} {g = Y.represents}
      (Nat-pathp _ _ λ a → Hom-pathp-reflr (Sets _)
        {A = F .F₀ a} {q = λ i → el! (C.Hom a (objs i))}
        (funext λ x →
           ap (λ e → e .Sets.to) (ap-F₀-iso c-cat (Hom[_,-] C a) _) $ₚ _
        ·· sym (Y.rep.to .is-natural _ _ _) $ₚ _
        ·· ap Y.Rep.from (sym (X.rep.from .is-natural _ _ _ $ₚ _)
                       ·· ap X.Rep.to (C.idl _)
                       ·· X.Rep.ε _)))
     i
```

## As terminal objects

We begin to connect the idea of representing objects to other universal
constructions by proving this alternative characterisation of
representations: A functor $F$ is representable if, and only if, its
[category of elements](Cat.Instances.Elements.html) $\int F$ has a
[terminal object](Cat.Diagram.Terminal.html).

```agda
terminal-element→representation
  : {F : Functor (C ^op) (Sets κ)} → Terminal (∫ C F) → Representation F
terminal-element→representation {F} term = f-rep where
  module F = Functor F
  open Terminal term
```

From the terminal object in $\int F$^[Which, recall, consists of an
object $X : \cC$ and a section $F(X) : \Sets$], we obtain a natural
transformation $\eta_y : F(y) \to \hom(y,X)$, given componentwise by
interpreting each pair $(y, s)$ as an object of $\int F$, then taking
the terminating morphism $(y, s) \to (X, F(X))$, which satisfies (by
definition) $F(!)(F(X)) = s$. This natural transformation is
componentwise invertible, as the calculation below shows, so it
constitutes a natural isomorphism.

```agda
  nat : F => よ₀ C (top .ob)
  nat .η ob section = has⊤ (elem ob section) .centre .hom
  nat .is-natural x y f = funext λ sect → ap hom $ has⊤ _ .paths $ elem-hom _ $
    F.₁ (has⊤ _ .centre .hom C.∘ f) (top .section)   ≡⟨ happly (F.F-∘ _ _) _ ⟩
    F.₁ f (F.₁ (has⊤ _ .centre .hom) (top .section)) ≡⟨ ap (F.₁ f) (has⊤ _ .centre .commute) ⟩
    F.₁ f sect                                       ∎

  inv : ∀ x → Sets.is-invertible (nat .η x)
  inv x = Sets.make-invertible
    (λ f → F.₁ f (top .section))
    (funext λ x → ap hom $ has⊤ _ .paths (elem-hom x refl))
    (funext λ x → has⊤ _ .centre .commute)

  f-rep : Representation F
  f-rep .rep = top .ob
  f-rep .represents = C^.invertible→iso nat $
    componentwise-invertible→invertible nat inv
```

## Universal constructions

We now show a partial converse to the calculation above: That terminal
objects are representing objects for a particular functor. Consider, to
be more specific, the constant functor $F : \cC\op \to \Sets$ which
sends everything to the terminal set. When is $F$ representable?

Well, unfolding the definition, it's when we have an object $X : \cC$
with a natural isomorphism $\hom(-,X) \cong F$. Unfolding _that_, it's
an object $X$ for which, given any other object $Y$, we have an
isomorphism of sets $\hom(Y,X) \cong \{*\}$^[which varies naturally in
$Y$, but this naturality is not used in this simple case]. Hence, a
representing object for the "constantly $\{*\}$" functor is precisely a
terminal object. It turns out the

```agda
representable-unit→terminal
  : Representation (Const (el (Lift _ ⊤) (hlevel 2))) → Terminal C
representable-unit→terminal repr .Terminal.top = repr .rep
representable-unit→terminal repr .Terminal.has⊤ ob = retract→is-contr
  (Rep.from repr) (λ _ → lift tt) (Rep.η repr) (hlevel 0)
```
