<!--
```agda
open import 1Lab.Prelude

open import Algebra.Group.Cat.Base
open import Algebra.Group

open import Cat.Functor.Adjoint

open import Data.List.Properties
open import Data.Sum.Properties
open import Data.List.Base
open import Data.Dec.Base
open import Data.Sum.Base
```
-->

```agda
module Algebra.Group.Free.Words {ℓ} (A : Type ℓ) ⦃ _ : Discrete A ⦄ where
```

# Free groups in terms of words

While we have a generic [[construction of free groups|free group
construction]] as a higher inductive type, which has the correct
universal property of the free group on any [[set]], it's sometimes more
useful to have a "quotient-free" description of the elements of a free
group --- akin to what lists are to [[free monoids]]. There are a couple
cases where this comes up:

1. When showing that the free group on a [[discrete]] set is again discrete;
2. When showing that the unit map $\eta : A \to F(A)$ is injective.

In both of these cases, while it would strictly speaking be possible to
prove these directly from the universal property, this turns out to be
very complicated. If we can instead implement free groups as plain old
data, both become very easy!

The idea is the same as for monoids: we want to find a *normal form* for
expressions in a free group, and then prove that these normal forms are
closed under the group operations. Since a group is, in particular, a
monoid, we might start with saying that a normal form will be a list,
which handles both unit and associativity. But the elements of the free
group on $A$ can't simply be lists of $A$, since groups also have
inverses. So we'll define a **letter** to be an element of $A + A$, with
the left summand standing for the inclusion of a generator $a$, and with
the right summand being a *negated* generator $a\inv$; and we'll refer
to a list of letters as a **word**.

<!--
```agda
private instance
  _ : ∀ {n} → H-Level A (2 + n)
  _ = basic-instance 2 (Discrete→is-set auto)
```
-->

```agda
Letter Word : Type ℓ
Letter = A ⊎ A

Word = List Letter
```

<!--
```agda
private
  pattern pos x = inl x
  pattern neg x = inr x

private variable
  a b c : A
  x y z : Letter
  xs ys zs : Word
```
-->

Once again we hit a snag, though: if there are any $a : A$, then every
element of $F(A)$ has multiple *distinct* representations at the level
of words!  For an extreme example, even the unit can be represented
either as the empty word $[]$, or as $aa\inv$, or as $aaa\inv a\inv$,
etc. We can fix this in one of two ways:

1. We could declare, by taking a quotient, that any word $x aa\inv y$,
   with arbitrary prefix $x$ and suffix $y$, will be identical to the word
   $xy$, with the generator-inverse pair deleted.

   While this works, we're essentially right back where we started! we'd
   have to prove that (e.g.) our decision procedure for equality in
   $F(A)$ respects deleting pairs.

2. We simply rule out these pathological words by requiring that the
   elements of the free group are **reduced**. If we arrange for "being
   reduced" to be a proposition, then we retain decidable equality,
   since we're free to not compare the proofs!

Defining $F(A)$ in terms of reduced words does have one pretty major
downside, though: concatenation of words does not preserve reducedness,
so we (nominally) have to insert a "normalisation" step that cancels out
any new pairs. This requires being able to identify when adjacent
elements are opposites --- so $A$ *must* have decidable equality.

## Reduced words

While we could define "reduced" as "does *not* contain an adjacent
$aa\inv$ (or $a\inv a$) pair", working with negative data is generally
very annoying. So we'll instead seek an equivalent, positive definition
of reducedness. First, we'll need a helper function that inverts a
letter, so we can have a single case that excludes both the $aa\inv$ and
$a\inv a$ pairs.

```agda
opp : Letter → Letter
opp (pos x) = neg x
opp (neg x) = pos x
```

<!--
```agda
opp-invol : ∀ x → opp (opp x) ≡ x
opp-invol (pos x) = refl
opp-invol (neg x) = refl

module opp = Equiv (Iso→Equiv (opp , iso opp opp-invol opp-invol))
```
-->

Then, we define reducedness. Both the empty word and the word containing
a single letter are reduced, since there's nowhere for a pair to hide.

```agda
data Reduced : Word → Type ℓ where
  nil  : Reduced []
  one  : ∀ x → Reduced (x ∷ [])
```

The first nontrivial case, then, is when we have *two* elements $x$ and
$y$ at the front of a word $xs$. Not only must $x$ and $y$ *not* be
opposites, but $y$ should also not be adjacent to an $y\inv$ hiding in
$xs$ --- so we ask that the longer $y.xs$ be reduced, and not $xs$.

```agda
  cons : ∀ x (a≠ob : x ≠ opp y) (bxs : Reduced (y ∷ xs)) → Reduced (x ∷ y ∷ xs)
```

<!--
```agda
uncons-reduced : Reduced (x ∷ xs) → Reduced xs
uncons-reduced (one _)         = nil
uncons-reduced (cons _ a≠ob x) = x
```
-->

We can prove that this is a proposition by a simple pattern match; and,
since we can decide at any point in a word whether two adjacent elements
are opposites, we can also decide whether a word is reduced.

```agda
reduced-is-prop : is-prop (Reduced xs)
reduced-is-prop nil     nil      = refl
reduced-is-prop (one a) (one .a) = refl
reduced-is-prop (cons a p xs) (cons .a q ys) =
  ap₂ (cons a) prop! (reduced-is-prop xs ys)

dec-reduced : ∀ xs → Dec (Reduced xs)
dec-reduced [] = yes nil
dec-reduced (x ∷ []) = yes (one x)
dec-reduced (x ∷ y ∷ xs) with x ≡? opp y | dec-reduced (y ∷ xs)
... | yes p | _  = no λ where
  (cons _ ¬p _) → ¬p p
... | no ¬p | yes a = yes (cons x ¬p a)
... | no ¬p | no ¬a = no λ a → ¬a (uncons-reduced a)
```

<!--
```agda
instance
  _ : ∀ {n} → H-Level (Reduced xs) (suc n)
  _ = prop-instance reduced-is-prop

  _ : ∀ {xs} → Dec (Reduced xs)
  _ = dec-reduced _
```
-->

## Implementing the group operation

As discussed before, the group operation in $F(A)$ can not simply be
concatenation of words --- we should cancel out an inner pair $a\inv a$,
for example, when concatenating the words $ba\inv$ and $ac$, to get
$bc$. We could implement a normalisation procedure, and define the group
operation $w\star w'$ to be the normal form of $ww'$ --- but this would
traverse the second word even though it does not need to! The only place
where a cancellable pair can arise when concatenating *reduced* words is
at the boundary.

Instead, we'll show that every letter $a$ induces an automorphism on the
set of reduced words, a sort of "reducing cons", which automatically
cancels an opposing element at the head of the word if necessary. By
iterating this procedure, we will obtain the group operation on $F(A)$.

```agda
act : Letter → Word → Word
act x [] = x ∷ []
act x (y ∷ xs) with x ≡? opp y
... | yes _ = xs
... | no  _ = x ∷ y ∷ xs
```

We can demonstrate the behaviour of this function with the following
helper lemma, saying that $a\inv$ acts on $a.w$ to give back $w$. A
similar case bash shows that $a$ acts on *reduced* words, too.

```agda
act-opp-head : act (opp x) (x ∷ xs) ≡ xs
act-opp-head {x = x} with opp x ≡? opp x
... | no ¬r = absurd (¬r refl)
... | yes _ = refl

act-is-reduced : ∀ x → Reduced xs → Reduced (act x xs)
act-is-reduced x nil = one x
act-is-reduced x (one a) with x ≡? opp a
... | yes p = nil
... | no ¬p = cons x ¬p (one a)
act-is-reduced x (cons a p ys) with x ≡? opp a
... | yes p = ys
... | no ¬p = cons x ¬p (cons a p ys)
```

<!--
```agda
act-reduced : Reduced (x ∷ xs) → act x xs ≡ x ∷ xs
act-reduced (one _) = refl
act-reduced (cons {y} x a≠ob p) with x ≡? opp y
... | yes a=ob = absurd (a≠ob a=ob)
... | no _     = refl
```
-->

The final ingredient we'll need about the `act`{.Agda}ion of each letter
is that it's invertible on the left, by the action of $a\inv$. This can
again be shown by a case bash.

```agda
act-opp : Reduced xs → act (opp x) (act x xs) ≡ xs
act-opp nil     = act-opp-head
act-opp {x = x} (one y) with x ≡? opp y
... | yes a = ap (_∷ []) (opp.adjunctr a)
... | no ¬a = act-opp-head
act-opp {x = x} (cons {y} x' a≠ob xs) with x ≡? opp x'
act-opp {x = x} (cons {y} x' a≠ob xs) | yes a=ob with opp x ≡? opp y
... | yes p = absurd (a≠ob (opp.adjunctl (sym a=ob) ∙ p))
... | no ¬p = ap (λ e → e ∷ y ∷ _) (opp.adjunctr a=ob)
act-opp {x = x} (cons {y} x' a≠ob xs) | no ¬p with opp x ≡? opp x
... | yes _ = refl
... | no ¬r = absurd (¬r refl)
```

We define the group operation by letting each letter of the left word
act on the right word, in turn. By induction on the left word, we can
extend the lemma above to say that reduced words are closed under
multiplication.

```agda
mul : Word → Word → Word
mul [] xs       = xs
mul (x ∷ xs) ys = act x (mul xs ys)

mul-reduced : ∀ xs → Reduced ys → Reduced (mul xs ys)
mul-reduced []       x  = x
mul-reduced (x ∷ xs) ys = act-is-reduced x (mul-reduced xs ys)
```

The simple recursive definition of `mul`{.Agda} is also compatible with
concatenation of words, in the sense that a concatenation $w.w'$ acts on
a word $z$ as though you had first let $w'$ act on $z$, and then applied
$w$ on the result.

```agda
mul-++ : ∀ xs → mul (xs ++ ys) zs ≡ mul xs (mul ys zs)
mul-++ []       = refl
mul-++ (x ∷ xs) = ap (act x) (mul-++ xs)
```

<details>
<summary>Using this comparison with composition of automorphisms, we can
show that, as long as the list $z$ is reduced, the group operation
`mul`{.Agda} is associative. Since it is definitionally unital on the
left, all that remains to construct of the group structure are the
inverses.</summary>

```agda
mul-assoc : ∀ xs → Reduced zs → mul (mul xs ys) zs ≡ mul xs (mul ys zs)
mul-assoc [] red = refl
mul-assoc (x ∷ xs) red = comm x (mul xs _) red ∙ ap (act x) (mul-assoc xs red) where
  comm : ∀ x xs → Reduced ys → mul (act x xs) ys ≡ act x (mul xs ys)
  comm x [] red = refl
  comm x (y ∷ xs) red with x ≡? opp y
  ... | yes a = sym (ap (λ e → act e (act y (mul xs _))) a ∙ act-opp (mul-reduced xs red))
  ... | no _  = refl
```
</details>

## Inverses and nonreducedness

As one might expect, the inverse of a word $w$ is computed by inverting
each letter, and then reversing the entire thing. It's actually pretty
straightforward, if not a bit tedious, to prove that this is a correct
definition of inverse, at least when the input word is reduced.

```agda
inv : Word → Word
inv []       = []
inv (x ∷ xs) = inv xs ∷r opp x

act-inv : Reduced xs → mul (inv xs) xs ≡ []
act-inv nil = refl
act-inv (one x) = act-opp-head
act-inv (cons {x} {xs} y a≠ob α) =
  mul ⌜ (inv xs ++ opp x ∷ []) ++ opp y ∷ [] ⌝ (y ∷ x ∷ xs) ≡⟨ ap! (++-assoc (inv xs) _ _) ⟩
  mul (inv xs ++ opp x ∷ opp y ∷ []) (y ∷ x ∷ xs)           ≡⟨ mul-++ (inv xs) ⟩
  mul (inv xs) (act (opp x) ⌜ act (opp y) (y ∷ x ∷ xs) ⌝)   ≡⟨ ap! (act-opp-head {y}) ⟩
  mul (inv xs) ⌜ act (opp x) (x ∷ xs) ⌝                     ≡⟨ ap! act-opp-head ⟩
  mul (inv xs) xs                                           ≡⟨ act-inv (uncons-reduced α) ⟩
  []                                                        ∎
```

The trouble comes when proving that inverting a word results in another
reduced word --- `inv`{.Agda} is appending elements on the right, but we
can only build reduced words by appending on the left. To bridge this
gap, we'll actually take a surprisingly classical detour: instead of
proving that `inv`{.Agda} preserves reducedness, we'll prove the
contrapositive --- it *reflects nonreducedness*.

Again, we'll need an inductive definition saying that a word is *not*
reduced. We can build a nonreduced word by appending an opposite pair at
the front, or by finding a nonreduced pair in the tail.

```agda
data Nonreduced : Word → Type ℓ where
  here  : ∀ ys t {t'} (t=ot : t' ≡ opp t) → Nonreduced (t' ∷ t ∷ ys)
  there : ∀ {x} (nrxs : Nonreduced xs)    → Nonreduced (x ∷ xs)
```

It's straightforward to show that if a word is not reduced, then it is
`Nonreduced`{.Agda}, since we can decide at each point whether we have
an inverse pair, and finding *no* such pairs would contradict the
assumption of reducedness.

```agda
to-nonreduced : ¬ Reduced xs → Nonreduced xs
to-nonreduced {[]} ¬red = absurd (¬red nil)
to-nonreduced {x ∷ []} ¬red = absurd (¬red (one x))
to-nonreduced {x ∷ y ∷ xs} ¬red =
  let
    work : x ≠ opp y → Nonreduced (x ∷ y ∷ xs)
    work x≠y = there (to-nonreduced {y ∷ xs} (λ red → ¬red (cons x x≠y red)))
  in Dec-rec (here xs y) work auto
```

The converse, that nonreducedness implies not being reduced, is simple:
an element of `Nonreduced`{.Agda} serves as an index, letting us
contradict a specific constructor of `Reduced`{.Agda}.

```agda
from-nonreduced : Nonreduced xs → ¬ Reduced xs
from-nonreduced (here ys t t=ot) (cons _ a≠ob red) = a≠ob t=ot
from-nonreduced (there nre) (cons _ a≠ob red)      = from-nonreduced nre red
```

The force of this definition comes from the following lemma, an
*inversion* principle for `Nonreduced`{.Agda} with concatenation on the
right. Let's walk through the type: it says that, if we have some prefix
$xs$, and the index of an inverse pair in the larger word $xs.x.ys$, we
can either find an inverse pair in $xs.x$ --- i.e., $x$ is inverse to
the last element in $xs$ --- or in $x.ys$, i.e. it it is inverse to the
head of $ys$.

```agda
split-nonreduced
  : ∀ xs → Nonreduced (xs ++ x ∷ ys)
  → Nonreduced (xs ∷r x) ⊎ Nonreduced (x ∷ ys)
```

<details>
<summary>The proof is actually just a case bash.</summary>

```agda
split-nonreduced [] x = inr x
split-nonreduced (y ∷ []) (here _ _ x) = inl (here [] _ x)
split-nonreduced (y ∷ []) (there x) = inr x
split-nonreduced (x ∷ y ∷ xs) (here _ _ p) = inl (here _ _ p)
split-nonreduced (x ∷ y ∷ xs) (there nre) with split-nonreduced (y ∷ xs) nre
... | inl p = inl (there p)
... | inr p = inr p
```

</details>

We can then prove that, if there is an inverse pair in the inverse
$xs\inv$ of a word $xs$, we can find an inverse pair in the original
list. The proof is a straightforward induction, first (trivially) ruling
out the case where the list has a single element.

```agda
inv-nonreduced : ∀ xs → Nonreduced (inv xs) → Nonreduced xs
inv-nonreduced (x ∷ []) (there ())
```

If we have a pair $xy$ in the inverse $x.y.xs$, we then have two cases
to consider, by the inversion principle above. Either the word $xy$ is
nonreduced, in which case we've found what we're looking for (the
`here'`{.Agda} case), or the inverse of $y.xs$ is nonreduced, in which
case (`there'`{.Agda}) we proceed by induction.

```agda
inv-nonreduced (x ∷ y ∷ xs) p =
  let
    here' : Nonreduced (opp y ∷ opp x ∷ []) → Nonreduced (x ∷ y ∷ xs)
    here' = λ where
      (there (there ()))
      (here _ _ p) → here xs y (sym (opp.adjunctr (opp.injective p)))

    there' : Nonreduced (inv (y ∷ xs)) → Nonreduced (x ∷ y ∷ xs)
    there' p = there (inv-nonreduced (y ∷ xs) p)

    p' : Nonreduced (inv xs ∷r opp y) ⊎ Nonreduced (opp y ∷ opp x ∷ [])
    p' = split-nonreduced (inv xs) (subst Nonreduced (++-assoc (inv xs) _ _) p)
  in [ there' , here' ] p'
```

By the contrapositive, `inv`{.Agda} preserves reducedness, so we can put
together a group structure.

```agda
inv-reduced : Reduced xs → Reduced (inv xs)
inv-reduced = contrapose λ ¬ixsr → from-nonreduced
  (inv-nonreduced _ (to-nonreduced ¬ixsr))
```

<!--
```agda
private
  module m = make-group
```
-->

```agda
  mkg : make-group (Σ[ l ∈ Word ] Reduced l)
  mkg .m.group-is-set = hlevel 2

  mkg .m.unit                = []      , nil
  mkg .m.mul (x , p) (y , q) = mul x y , mul-reduced x q
  mkg .m.inv (x , p)         = inv x   , inv-reduced p

  mkg .m.assoc (x , _) (y , _) (z , r) = Σ-prop-path! (sym (mul-assoc x r))
  mkg .m.invl (_ , x)                  = Σ-prop-path! (act-inv x)
  mkg .m.idl _                         = refl
```

<!--
```agda
Free-group : Group ℓ
Free-group = to-group mkg

open Free-object
```
-->

## The universal property

We're almost done with the case bashes, but now we have to provide a
universal property for the group we've constructed. Fortunately, we have
a convenient API for [[free objects]] which tells us what we have to
define. First, we have the group itself, and we send a generator $a$ to
the word consisting of exactly $a$.

```agda
make-free-group : Free-object Grp↪Sets (el! A)
make-free-group .free = Free-group
make-free-group .unit = λ x → pos x ∷ [] , one _
```

Next, if we have a group $G$ and a function $f : A \to G$ from the set
of generators, we must extend this to a group homomorphism $F(A) \to G$.
We'll also do this by recursion on the words, sending letters to
automorphisms of $G$. First, we can send a letter $a$ to the map $x
\mapsto f(a)x$, and similarly $a\inv$ to $x \mapsto f(a)\inv x$. By
recursion, we extend this to mapping words, sending the empty word to
the unit.

```agda
make-free-group .fold {G} f = ∫hom (λ (xs , _) → go xs) pres module fold where
  module G = Group-on (G .snd)
  open G using (_⋆_ ; _⁻¹) public

  goL : Letter → ⌞ G ⌟ → ⌞ G ⌟
  goL (pos x) g = f x ⋆ g
  goL (neg x) g = f x ⁻¹ G.⋆ g

  go : Word → ⌞ G ⌟
  go []       = G.unit
  go (x ∷ xs) = goL x (go xs)
```

<details>
<summary>Then, we must prove that this preserves the group operation.
This turns out to be a handful of case bashes, appealing to the group
laws in $G$, so we trust that the reader can follow the proofs below.
</summary>

```agda
  go-opp : ∀ x y g → x ≡ᵢ opp y → goL x (goL y g) ≡ g
  go-opp (pos x) (neg .x) g reflᵢ = G.cancell G.inverser
  go-opp (neg x) (pos .x) g reflᵢ = G.cancell G.inversel

  go-ass : ∀ x g h → goL x (g ⋆ h) ≡ goL x g ⋆ h
  go-ass (pos x) g h = G.associative
  go-ass (neg x) g h = G.associative

  go-letter : ∀ x xs → go (act x xs) ≡ goL x (go xs)
  go-letter x [] = refl
  go-letter x (y ∷ xs) with x ≡? opp y
  ... | yes p = sym (go-opp x y _ (Id≃path.from p))
  ... | no ¬p = refl

  go-mul : ∀ xs ys → go (mul xs ys) ≡ go xs ⋆ go ys
  go-mul [] ys = sym G.idl
  go-mul (x ∷ xs) ys =
    go (act x (mul xs ys))  ≡⟨ go-letter x (mul xs _) ⟩
    goL x (go (mul xs ys))  ≡⟨ ap (goL x) (go-mul xs ys) ⟩
    goL x (go xs ⋆ go ys)   ≡⟨ go-ass x (go xs) (go ys) ⟩
    (goL x (go xs) ⋆ go ys) ∎

  pres : is-group-hom _ _ (λ (xs , _) → go xs)
  pres .is-group-hom.pres-⋆ (x , p) (y , q) = go-mul x y
```

</details>

We must then prove that folding the singleton word $a$ with a function
$f$ gives the result $f(a)$ --- we almost got it definitionally, but the
computation above produces the identical $f(a) * 1$ instead.

```agda
make-free-group .commute {_ , Y} = ext λ a → Group-on.idr Y
```

Finally, we must prove that our fold is the unique group homomorphism
with this property. This turns out to be --- you guessed it --- a ton
more case bashes. First, we'll show that a group homomorphism $g : F(A)
\to G$ which sends the singleton list to $f(a)$ agrees with our fold on
letters.

```agda
make-free-group .unique {Y} {f} g h = ext uniq where
  open fold {Y} f
  module g = is-group-hom (g .snd)

  g-one : ∀ x → g · (x ∷ [] , one x) ≡ goL x G.unit
  g-one (pos x) =
    g · (pos x ∷ [] , one (pos x)) ≡⟨ happly h x ⟩
    f x                            ≡⟨ G.intror refl ⟩
    f x ⋆ G.unit                   ∎
  g-one (neg x) =
    g · (neg x ∷ [] , one (neg x))    ≡⟨ g.pres-inv {pos x ∷ [] , one _} ⟩
    g · (pos x ∷ [] , one (pos x)) ⁻¹ ≡⟨ ap G.inverse (happly h x) ⟩
    f x ⁻¹                            ≡⟨ G.intror refl ⟩
    f x ⁻¹ ⋆ G.unit                   ∎
```

For positive generators, this is almost by definition, minding our extra
unit on the right as above; for the negative case, we use that a group
homomorphism commutes with the inverse. Then, we can extend this to show
that $g$ takes a word $x.w$ to the result of letting $x$ act on $g(w)$
by our fold above. This is by cases on the evidence that the word is
reduced.

```agda
  g-cons : ∀ x xs α → g · (x ∷ xs , α) ≡ goL x (g · (xs , uncons-reduced α))
  g-cons (pos x) [] (one .(pos x)) =
    g · (pos x ∷ [] , one (pos x)) ≡⟨ happly h x  ⟩
    f x                            ≡⟨ G.intror g.pres-id ⟩
    f x ⋆ g · ([] , nil)           ∎
  g-cons (neg x) [] (one .(neg x)) =
    g · (neg x ∷ [] , one (neg x))    ≡⟨ g.pres-inv {pos x ∷ [] , one _} ⟩
    g · (pos x ∷ [] , one (pos x)) ⁻¹ ≡⟨ ap G.inverse (happly h x) ⟩
    f x ⁻¹                            ≡⟨ G.intror g.pres-id ⟩
    f x ⁻¹ ⋆ g · ([] , nil)        ∎
  g-cons x (y ∷ xs) α@(cons _ _ β) =
    g · (x ∷ y ∷ xs , α)                    ≡⟨ ap₂ (λ e α → g .fst (e , α)) (sym (act-reduced α)) prop! ⟩
    g · (act x (y ∷ xs) , _)                ≡⟨ g.pres-⋆ (x ∷ [] , one _) (y ∷ xs , β) ⟩
    g · (x ∷ [] , _) ⋆ g · (y ∷ xs , β)     ≡⟨ ap₂ G._⋆_ (g-one x) (g-cons y xs β) ⟩
    goL x G.unit ⋆ goL y (g · (xs , _))     ≡˘⟨ go-ass x G.unit (goL y (g · _)) ⟩
    goL x (G.unit ⋆ goL y (g · (xs , _)))   ≡⟨ ap (goL x) (G.idl ∙ sym (g-cons y xs β)) ⟩
    goL x (g · (y ∷ xs , β))                ∎
```

Finally, we can put this together for an arbitrary reduced word, using
the lemmas above for each case.

```agda
  uniq : ∀ xs (α : Reduced xs) → g · (xs , α) ≡ go xs
  uniq xs nil     = g.pres-id
  uniq xs (one a) =
    g · (a ∷ [] , one a)    ≡⟨ g-cons _ _ (one a) ⟩
    goL a (g · ([] , nil))  ≡⟨ ap (goL a) g.pres-id ⟩
    goL a G.unit            ∎
  uniq (a ∷ b ∷ xs) (cons a x α) =
    g · (a ∷ b ∷ xs , cons a x α)  ≡⟨ g-cons _ _ (cons a x α) ⟩
    goL a (g · (b ∷ xs , α))       ≡⟨ ap (goL a) (uniq (b ∷ xs) α) ⟩
    goL a (goL b (go xs))          ∎
```
