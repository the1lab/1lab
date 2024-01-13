---
customtitle: Introduction to HoTT
---

<!--
```agda
open import 1Lab.Prelude hiding (fibre)
```
-->

```agda
module 1Lab.intro where
```

# Introduction

This page aims to present a first introduction to cubical type theory,
from the perspective of a mathematician who has heard about type theory
but has no previous familiarity with it. Specifically, the kind of
mathematician that we are appealing to is one who is familiar with some
of the ideas in category theory and homotopy theory --- however, the
text also presents the concepts _syntactically_, in a way that can be
read without any prior mathematical knowledge.

Note that whenever code appears, all of the identifiers are hyperlinked
to their definitions, which are embedded in articles that describe the
concepts involved. For instance, in the code block below, you can click
the symbol `≡`{.Agda} to be taken to the page on path types.

```agda
_ : 2 + 2 ≡ 4
_ = refl
```

For some operations, we use the built-in Agda definitions, which do not
have explanations attached. This is the case for the `+`{.Agda}
operation above. However, in any case, those definitions are either
built-ins (in which case only the type matters), or defined as
functions, in which case the implementation is visible. The most
important built-ins for Cubical Agda, and those most likely to lead you
to a built-in Agda page, have their own explanations, linked below:

- The [`1Lab.Path`] page explains the primitives `I`, `i0`, `i1`, `_∧_`,
`_∨_`, `~`, `PathP`, `Partial`, `_[_↦_]`, and `hcomp`.

[`1Lab.Path`]: 1Lab.Path.html

- The [`1Lab.Univalence`] page explains the primitives `Glue`, `glue`,
`unglue`.

[`1Lab.Univalence`]: 1Lab.Univalence.html

With that out of the way, the first thing to do is the aforementioned
refresher on type theory. **If you're already familiar with type theory,
feel free to skip to [What's next?](#what-next)**. If you're not
familiar with some of the connections that HoTT has to other areas of
mathematics, like higher category theory and topology, I recommend that
you read the type theory section anyway!

<details terminology>
<summary>On the term "homotopy type theory".</summary>

The text below refers to the foundational system that it is presenting
as "homotopy type theory", while it would be technically more correct to
refer to it as **a** homotopy type theory. HoTT is not a specific type
theory, but a family of type theories that put emphasis on the
homotopy-theoretic interpretation of type theory. In particular, a
homotopy type theory is expected to validate univalence and have some
class of higher inductive types.

Below, we describe _cubical type theory_, which is one particular
homotopy type theory. In cubical type theory, we interpret types as the
Kan complices in the category of De Morgan cubical sets,
$\rm{PSh}(\square)$. This interpretation gives rise to a model
structure on the category of cubical sets, referred to as a
"cubical-type model structure".

</details>

# Type theory

::: warning
The text below is subject to change! It's still very much a
document in flux. In particular, the type theory section doesn't talk
about induction, which is something that will be expanded on in the
future.
:::

Type theory is a foundational system for mathematics which, in contrast
to a set-theoretic foundation like ZFC, formalises mathematical
_constructions_ rather than mathematical _proofs_. That is, instead of
specifying which logical deductions are valid, and then giving a set of
axioms which characterise the behaviour of mathematical objects, a
type-theoretic foundation specifies directly which mathematical
constructions are valid.

Formally speaking, it is impossible to _construct_ objects in set
theoretic foundations; Rather, one can, by applying the deduction rules
of the logical system and appealing to the axioms of the set theory,
prove that an object with the desired properties exists. As an example,
if we have a way of referring to two objects $x$ and $y$, we can _prove
that there exists_ a set representing the ordered pair $(x, y)$, using
the axiom of pairing. Writing quasi-formally, we could even say that
this set is constructed using the expression $\{x, \{x, y\} \}$, but
this is only a notational convenience.

In contrast, a type-theoretic foundational system, such as <span
class=abbrev title="Homotopy Type Theory">HoTT</span> (what we use
here), specifies directly how to _construct_ mathematical objects, and
proving a theorem becomes a special case of constructing an object.  To
specify what constructions are well-behaved, we sort the mathematical
objects into boxes called _types_. Just like in set theory, the word
"set" is a primitive notion, in type theory, the word "type" is a
primitive notion. However, we can give an intuitive explanation: "A type
is a thing that things can be". For instance, things can be natural
numbers, but things can not be "two" --- hence, the natural numbers are
a type, but two is not. Formally, a type is specified by giving:

* A **formation rule**, which tells us which expressions denote valid
types at all. For instance, the formation rule for product types tells
us that $\bb{N} \times \bb{N}$ denotes a well-formed type, but
"$\bb{N} \times \to$" does not. The formation rules also have the
duty of preventing us from running into _size issues_ like Russell's
paradox, by constraining the use of [universes](#universes).

* A handful of **introduction rules**, which tell us how to piece
previously-constructed objects together to form an object of a
different type. Sticking with products as an example, if we have
previously constructed objects called $a$ and $b$, we can construct an
ordered pair $(a, b)$.

  Since the introduction rules are inseparable from their types, it is
  impossible to construct an object without knowing in which type it
  lives. If we used the rule which introduces ordered pairs, we know for
  sure that we built an object of the product type. To specify that an
  object lives in a certain type, we use the notation $a : A$ --- which
  can be read as "$a$ **inhabits** $A$", or "$a$ **is a point of** $A$",
  or "$a$ **has type** $A$".

  The notation for stating inhabitation agrees with mathematical parlance
  in when both make sense. For example, a function from the reals to the
  reals is commonly introduced with the notation $f : \bb{R} \to
  \bb{R}$. In type theory, this is made formal as a typing
  declaration: $f$ is a point of the type of functions $\bb{R} \to
  \bb{R}$, hence we know that the rules of function types can be
  used with $f$. However, when introducing a more complex object, we're
  forced to break into informality and conventional shorthand: "Let G be
  a group". In HoTT, we can directly write $G : \rm{Group}$[^allgroups],
  which tells us that the rules for the type of groups apply to $G$.

[^allgroups]: As usual, we do not have a type of _all_ groups. Instead,
we have a family of types of groups that depends on how "big" their
underlying type is allowed to be: what [universe](#universes) it lives
in.

* A handful of **elimination rules**, which say how inhabitants of that
type can be manipulated. Keeping with the running example, the product
type has elimination rules corresponding to projecting either the first
or second component of a pair.

  Furthermore, each elimination rule comes with specified behaviour for
  when it "interacts" with the introduction rules, a process which we
  generally call _reduction_. Repeatedly applying these "interactions"
  tells us how a given construction can have _computational behaviour_
  --- by performing a delicate dance of elimination and introduction, we
  can go from $2 + 2$ to $4$.

Now that we have an intuitive motivation for the notions of type theory,
we can more precisely discuss the structure of _formal_ type theory and
how it differs from formal (material) set theory. The first (and perhaps
most important) difference is that formal set theory is a "two layered"
system, but type theory only has "one layer". In (for example) <span
class=abbrev title="Zermelo-Fraenkel set theory with Choice">ZFC</span>,
we have the deductive framework of first-order logic (the "first
layer"), and, using the language of that logical system, we assert the
axioms of set theory. This remains valid if we switch set theories: For
instance, <span class=abbrev title="Intuitionistic Zermelo-Fraenkel set
theory">IZF</span> would substitute first-order logic with first-order
_intuitionistic_ logic, and remove the assertion that the axiom of
choice holds.

In contrast, type theory only has one layer: The layer of types. What in
formal set theory would be a deduction in FOL, in type theory becomes
the construction of an inhabitant of a certain type, where propositions
are identified with certain types as in the table below. Note that up to
a first approximation, we can read each type former as denoting a
specific _set_, or as denoting a specific _space_.

<div class="overflow-x: auto; overflow-y: hidden; width: 100%">
| Types                 | Logic                  | Sets                            | Spaces                    |
|-----------------------|------------------------|---------------------------------|---------------------------|
| $A$                   | proposition            | set                             | space                     |
| $a : A$               | proof                  | element                         | point                     |
| $B(x)$                | predicate              | family of sets                  | fibration                 |
| $b(x) : B(x)$         | conditional proof      | family of elements              | section                   |
| $\bot, \top$          | $\bot, \top$           | $\emptyset, \{\emptyset\}$      | $\emptyset, \{*\}$        |
| $A \times B$          | $A \land B$            | Cartesian product               | product space             |
| $A \uplus B$          | $A \lor B$             | disjoint union                  | coproduct space           |
| $A \to B$             | $A \to B$              | function set                    | function space            |
| $\prod_{(x : A)}B(x)$ | $\forall{(x : A)}B(x)$ | n-ary product                   | space of sections         |
| $\sum_{(x : A)}B(x)$  | $\exists{(x : A)}B(x)$ | n-ary disjoint union            | total space               |
| $x \equiv_A y$        | equality $x = y$       | diagonal $\{ (x,x) : x \in A\}$ | path space $A^\bb{I}$     |
</div>

This segues nicely into another difference between type theory and set
theory, which concerns the setup of their deductive systems. A deductive
system is a specification for how to derive **judgements** using
**rules**. We can think of the deductive system as a game of sorts,
where the judgements are to be thought of as board positions, and the
rules specify the valid moves.

In the deductive system of first-order logic, there is only one kind of
judgement, stating that a proposition has a proof. If $A$ is a
proposition, then the judgement "$A$ has a proof" is written "$\vdash
A$". Note that the judgement $\vdash A$​ is a part of the *meta*theory,
and the proposition $A$ is a part of the theory itself. That is, $\vdash
A$ is an **external** notion, and $A$ is an **internal** notion.

In type theory, the basic judgement is inhabitation, written $\vdash a :
A$.  If $A$ is a type that denotes a proposition, then this is analogous
to the judgement $\vdash A$ of first-order logic, and we refer to $a$ as
a _witness_ of $A$, or simply as a proof of $A$. Even better, if $A$ is
a purely logical proposition such that $\vdash A$ holds without any
appeal to the principle of excluded middle, then there is a term $a$ for
which $\vdash a : A$ holds in type theory.

When $A$ is being thought of as a collection of things, we might imagine
that $a : A$ is analogous to $a \in A$. However, this is not the case:
While $a \in A$ is a _proposition_ (an internal statement), $a : A$ is a
_judgement_, an external statement. That is, we can not use $a : A$ with
the propositional connectives mentioned in the table above --- we can
not make statements of the form "if it is not the case that $a : A$,
then $b : B$". This is the second difference we will mention between set
theory and type theory: The _proposition_ $a \in A$ is an internal
relation between previously-constructed terms $a$ and $A$, but the
external judgement $\vdash a : A$ is indivisible, and it does not make
sense to talk about $a$ without also bringing up that it's in $A$.

The third and final difference is the treatment of equality, which is
arguably also the most important part of homotopy type theory. In set
theory, given sets $a$ and $b$, we have a proposition $a = b$, which is
given meaning by the _axiom of extensionality_: $a = b$ whenever $a$ and
$b$ behave the same with respect to $\in$. Correspondingly, in type
theory, we have an equality _type_, written $a \equiv_A b$ (where $a, b
: A$), giving us the internal notion of equality. But we also have an
external notion of equality, which encodes the aforementioned
interactions between introduction and elimination rules. This is written
$\vdash a = b : A$, and it's meant to indicate that $a$ and $b$ are the
same _by definition_ --- hence we call it **definitional equality**.

Since definitional equality is a judgement, it's also not subject to the
internal propositional connectives --- we can not prove, disprove,
assume or negate it when working inside type theory, for it does not
make sense to say "if $a$ and $b$ are equal by definition, then [...]".
Correspondingly, in the Agda formalisation, definitional equality is
invisible, since it's represented by the computation rules of the type
theory.

In the rest of this section, we will recall the presentation of the most
ubiquitous types. The idea is that if you've encountered type theory
before, then skimming the explanation here should help snap your mind
back into focus, while if this is your first time interacting with it,
then the content here should be enough for you to understand the rest of
the 1lab development.

# Functions

If we have two previously-constructed types $A$ and $B$, we can form the
type of **functions from $A$ to $B$**, written $A \to B$. Often,
functions will also be referred to as **maps**. A function is,
intuitively, a rule prescribing how to obtain an inhabitant of $B$ given
an inhabitant of $A$. In type theory, this is not only an intuition, but
rather a _definition_. This is in contrast with set theory, where
functions are defined to be relations satisfying a certain property.

Given a function $f : A \to B$, we can **apply** it to an inhabitant
$a : A$, resulting in an inhabitant $f\ a$ of the codomain $B$, called
the **value of $f$ at $a$**. For clarity, we sometimes write $f(a)$ for
the value of $f$ at $a$, but in Agda, the parentheses are not necessary.

The most general form for constructing an inhabitant of $A \to B$ is
called **lambda abstraction**, and it looks like $(\lambda (x : A). e)$,
though shorthands exist. In this construction, the subexpression $e$
denotes the _body_ of a function definition, and $x$ is the parameter.
You can, and should, think of the expression $\lambda x. e$ as being the
same as the notation $x \mapsto e$ often used for specifying a map.
Indeed, Agda supports definition of functions using a more traditional,
"rule-like" notation, as shorthand for using $\lambda$ abstraction. For
instance, the following definitions of inhabitants `f` and `g` of
$\rm{Nat} \to \rm{Nat}$ are definitionally the same:

<div class=mathpar>
<figure>
<!--
```agda
module _ where private
```
-->
```agda
  f : Nat → Nat
  f x = x * 3
  -- Function definition
  -- with a "rule".
```
</figure>

<figure>
<!--
```agda
module _ where private
```
-->
```agda
  g : Nat → Nat
  g = λ x → x * 3
  -- Function definition
  -- with λ abstraction
```
</figure>
</div>

In general, we refer to a way of constructing an inhabitant of a type as
an _introduction rule_, and to a way of consuming an inhabitant of a
type as an _elimination rule_. Concisely, the introduction rule for $A
\to B$ is $\lambda$ abstraction, and the elimination rule is function
application. A general principle of type theory is that whenever an
elimination rule "meets" an introduction rule, we must describe how they
interact.

In the case of $\lambda$-abstraction meeting function application, this
interaction is called _$\beta$-reduction_[^betaredex], and it tells us
how to compute a function application. This is the usual rule for
applying functions defined by rules: The value of $(\lambda x.\ e) e'$
is $e$, but with $e'$ replacing $x$ whenever $x$ appears in $e$. Using
the notation that you'd find in a typical[^newoldlang] type theory
paper, we can concisely state this as:

$$
(\lambda x.\ e) e' \longrightarrow e[e'/x]
$$

[^betaredex]: Consequently, a term of the form $(\lambda x.\ e) e'$ is
referred to as a _$\beta$ redex_ (plural _$\beta$ redices_), short for
_$\beta$-reducible expression_, but since we're not really interested in
the theory of programming languages here, this terminology will not come
up.

[^newoldlang]: A survey paper of POPL proceedings by Guy L. Steele
[@Steele2017] identified **twenty-eight** different notations for
substitution, so the word "typical" is.. questionable, at best.

In addition, function types enjoy a definitional _uniqueness_ rule,
which says "any function is a $\lambda$ expression". Symbolically, this
means that if we have $f : A \to B$, the terms $f$ and $(\lambda x.\ f\
x)$ are equal, definitionally. This is called $\eta$-equality, and when
applied right-to-left as a reduction rule, $\eta$-reduction.

Functions of multiple arguments are defined by iterating the unary
function type. Since functions are types themselves, we can define
functions whose codomain is another function --- where we abbreviate $A
\to (B \to C)$ by $A \to B \to C$. By the uniqueness rule for function
types, we have that any inhabitant of this type is going to be of the
form $\lambda x.\ \lambda y.\ f\ x\ y$, which we abbreviate by $\lambda
x\ y.\ f\ x\ y$. In Agda, we can write this as `λ x y → ...`, or by
mentioning multiple variables in the left-hand side of a rule, as shown
below.

<!--
```agda
module _ where private
```
-->
```agda
  f : Nat → Nat → Nat
  f x y = x + 3 * y
```

# Universes

Instead of jumping right into the syntactic definition (and motivation)
for universes, I'm going to take a longer route, through _topos theory_
and eventually _higher_ topos theory, which gives a meaning explanation
for the idea of universes by generalising from a commonly-understood
idea: the correspondence between predicates and subsets. Initially, we
work entirely in the category of sets, assuming excluded middle for
simplicity. Then we pass to an arbitrary elementary topos, and finally
to an arbitrary higher topos. **If you don't want to read about
categories, [click here]**

[click here]: #universes-internally

First, let's talk about subsets. I swear I'm going somewhere with this,
so bear with me. We know that subsets correspond to predicates, but what
even is a subset?

* If we regard sets as _material_ collections of objects, equipped with
a membership relation $\in$, then $S$ is a subset of $T$ if every
element of $S$ is also an element of $T$. However, this notion does not
carry over directly to structural set theory (where sets are essentially
opaque objects of a category satisfying some properties), or indeed to
type theory (where there is no membership relation) --- but we can
salvage it.

  Instead of thinking of a subset directly as a subcollection, we define
  a subset $S \subseteq T$ to be an _injective function_ $f : S
  \hookrightarrow T$. Note that the emphasis is on the _function_ and
  not on the index set $S$, since we can have many distinct injective
  functions with the same domains and codomains (**exercise**: give two
  distinct subsets of $\bb{N}$ with the same domain[^points]).

  To see that this definition is a generalisation of the material
  definition in terms of $\in$, we note that any injective function $f :
  S \hookrightarrow T$ can be _restricted_ to a bijective function $f :
  S \xrightarrow{\sim} \rm{im}(f)$, by swapping the original codomain
  for the image of the function. Since the image is a subset of the
  codomain, we can interpret any injective $f : S \hookrightarrow T$ as
  expressing a _particular_ way that $S$ can be regarded as a subset of
  $T$.

[^points]: **Solution**: Recall what it means for a map to be injective
- that $f(a) = f(b) \to a = b$. If the domain of a function is a set
with a single point, then the consequent is automatically satisfied!
Since the maps $* \to \bb{N}$ are in 1-to-1 correspondence with
the elements of $\bb{N}$, we can consider _any two numbers_ to be
distinct subsets with the same domain.

* Alternatively, we can think of a subset as being a _predicate_ on the
larger set $T$, which holds of a given element $x$ when $x$ is in the
subset $S$. Rather than directly thinking of a predicate as a formula
with a free variable, we think of it as a _characteristic function_
$\chi : T \to \{0,1\}$, from which we can recover the subset $S$ as $\{
x \in T : \chi(x) = 1 \}$.

  This definition works as-is in structural set theory (where the
  existence of solution sets for equations --- called "equalisers" ---
  is assumed), but in a more general setting (one without excluded
  middle) like an arbitrary elementary topos, or indeed type theory, we
  would replace the 2-point set $\{0,1\}$ by an object of
  _propositions_, normally denoted with $\Omega$.

These two definitions are both appealing in their own right --- the
"subsets are injective functions" can be generalised to arbitrary
categories, by replacing the notion of "injective function" with
"monomorphism", while "subsets are predicates" is a very clean notion
conceptually. Fortunately, it is well-known that these notions coincide;
For the purposes of eventually generalising to universes, I'd like to
re-explain this correspondence, in a very categorical way.

Consider some sets $A, B$ and an arbitrary function $f : A \to B$
between them. We define the **fibre of $f$ over $y$** to be the set
$f^*(y) = \{ x \in A : f(x) = y \}$, that is, the set of points of the
domain that $f$ maps to $y$ --- in the context of set theory, this would
be referred to as the _preimage_ of $y$, but we're about to generalise
beyond sets, so the more "topological" terminology will be useful. We
can often characterise properties of $f$ by looking at all of its
fibres. What will be useful here is the observation that _the fibres of
an injective function have at most one element_.

More precisely, let $f : A \hookrightarrow B$ be injective, and fix a
point $y \in B$ so we can consider the fibre $f^*(y)$ over y. If we have
two inhabitants $a, b \in f^*(y)$, then we know (by the definition of
fibre) that $f(a) = y = f(b)$, hence by injectivity of $f$, we have $a =
b$ --- if $f^*(y)$ has any points at all, then it has exactly one. It
turns out that having at most one point in every fibre precisely
characterises the injective functions: Suppose $f(a) = f(b)$; Then we
have two inhabitants of $f^*(f(a))$, $a$ and $b$, but since we assumed
that $f^*(y)$ has at most one inhabitant for any $y$, we have $a = b$,
so $f$ is injective.

We call a set (type) $X$ with at most one element (at most one point) a
**subsingleton**, since it is a subset of the singleton set (singleton
type), or a **proposition**, since a _choice_ of point $x \in X$ doesn't
give you any more information than merely telling you "$X$ is inhabited"
would.  Since there is a 1-to-1 correspondence between subsingletons $X$
and propositions "$X$ is inhabited", the assignment of fibres $y \mapsto
f^*(y)$ defines a predicate $\chi_f : B \to \Omega$, where we have
implicitly translated between a subsingleton and its corresponding
proposition.[^hprops]

[^hprops]: In some foundational systems --- including HoTT, the one we
are discussing --- "subsingleton" is literally taken as the _definition_
of "proposition", so this translation isn't merely omitted, it's not
necessary at all.

Conversely, if we have such an assignment $\chi : B \to \Omega$, we
can make a map into $B$ with subsingleton fibres by carefully choosing
the domain. We take the domain to be the disjoint union of the family
$\chi$, that is, the set $\sum_{(x : B)} \chi(x)$. The elements of this
set can be described, moving closer to type-theoretic language, as pairs
$(i, p)$ where $i \in B$ and $p \in \chi(i)$ is a witness that the
subset predicate holds of $i$.

I claim: the map $\pi_1 : (\sum_{(x : B)} \chi(x)) \to B$ which takes
$(i, p) \mapsto i$ has subsingleton fibres. This is because an element
of $\pi^*_1(y)$ is described as a pair $(i , q)$, and since it's in the
fibre over $y$, we have $i = y$; Since $\chi$ (by assumption) takes
values in subsingletons, concluding that $i = y$ is enough to establish
that any two $(i, q)$ and $(i',q') \in \pi_1^*(y)$ must be equal.

The point of the entire preceding discussion is that the notions of
"injections into $B$" and "maps $B \to \Omega$" are equivalent, and,
more importantly, _this is enough to characterise the object
$\Omega$_[^subobjclass].

Let me break up this paragraph and re-emphasise, since it'll be the key
idea later: A **type of propositions** is precisely **a classifier for
maps with propositional fibres**.

Since the subobjects of $B$ are defined to be injections $X \to B$, and
maps $B \to \Omega$ represent these subobjects (in a coherent way), we
call $\Omega$ a **subobject classifier**, following in the tradition of
"classifying objects". A subobject classifier is great to have, because
it means you can talk about logical propositions --- and, in the
presence of functions, predicates --- as if they were points of a type.

<details>
<summary>More on general classifying objects.</summary>

A **classifying object** for some data is an object --- normally written
$B(\text{data})$ --- such that maps $X \to B(\text{data})$ correspond to
data "over" $X$, in the sense that the data admits some map into $X$.
Above, we were discussing the _subobject classifier_ that one can find
in an elementary topos; Maps $X \to \Omega$ (the object of propositions)
correspond to maps into $X$ with "propositional data".

To find another example in category theory, we pass to higher category
theory, i.e. $n$-category theory for high values of $n$, such as $n =
2$. As a 1-dimensional structure, we can consider the data of a category
$E$ _[[lying over|displayed category]]_ another category $B$ to be a
functor $E \to B$ which has certain [[lifting properties|cartesian map]]
- some sort of categorical _[[fibration|cartesian fibration]]_.

One would like to find a correspondence between these "categories over
categories" and some data that we already know how to conceptualise; It
turns out that Grothendieck fibrations over $B$ --- i.e., the functors
$F : E \to B$ satisfying said "certain lifting properties" ---
[correspond](Cat.Displayed.Cartesian.Indexing.html) to weak 2-functors
into $\rm{Cat}$.

Conversely, this equivalence lets us think of a family of categories
indexed by $B$ --- a 2-dimensional concept --- corresponds precisely to
1-dimensional data (a special class of functors between ordinary
categories). Furthermore, the equivalence is induced by a
construction on (weak 2-)functors --- the [[Grothendieck
construction|total category]], written $\int F$ --- that exactly mirrors
the disjoint union $\sum F$ that we used above!

To summarise:

- A classifying object $B(\text{data})$ is an object where maps $X \to
B(\text{data})$ corresponds to data over ("pointing towards") $X$.

- The kind of classifying objects that we care about here are ubiquitous
in all levels of $n$-category theory, but especially in $(n,1)$-category
theory, where some behave like universes of a given truncation level.

- Since the objects in a $n$-category act like $(n-1)$-categories, the
"most complex" classifier that a $n$-topos can have is for internal the
$(n-1)$-category of internal $(n-2)$-categories, and this all works
better in the case where we're actually talking about $(n,1)$-topoi.

</details>

[^subobjclass]: Let me make this more precise. In any (univalent)
category with [[finite limits]] $\mathscr{E}$, we have a functor $\rm{Sub} :
\mathscr{E}\op \to \set$, which takes $c$ to the full subcategory of
$\mathscr{E}/c$ on the injections. We say that $\Omega \in \mathscr{E}$
is a **subobject classifier** if there is a natural isomorphism
$\rm{Sub} \cong \hom(-,\Omega)$, i.e., if $\Omega$ is a representing
object for the subobject functor. Since the Yoneda lemma implies that
representing objects are unique, this characterises $\Omega$.

However, we often want to talk about _sets_ and _families of sets_ as if
they were points of a type, instead of just subsets. We could pass to a
higher category that has a **discrete object classifier** --- this would
be a "type of sets" ---, but then the same infelicity would be repeated
one dimension higher: we'd have a classifier for "sets", but our other
objects would look like "categories", and we wouldn't be able to
classify those!

<details>
<summary>**Take a moment** to convince yourself that the interpretation
of a discrete object classifier as a type of sets makes sense.</summary>

Note that we defined "proposition" to mean "at most one element". We can
generalise this to a notion which applies to categories by defining a
**discrete category** to be one that has _propositional hom-sets_, i.e.
one in which the only morphisms are identities. Note that a discrete
category is automatically a discrete _groupoid_, since the identity map
is an isomorphism.

A **discrete object classifier** (say $\set$) would then be a classifier
for functors which have discrete groupoids as fibres --- the fibres have
no categorical information, being nothing more than a set. Given any set
$X$, we'd have a name for it as the interpretation of the unique map
$\rm{Disc}(X) \to *$ as a map $* \to \set$. The name $\set$ was
chosen because in the $(2,1)$-category $\Grpd$, the discrete object
classifier is exactly the category of sets.

</details>

Thus we might hope to find, in addition to a subobject classifier, we
could have a general **object classifier**, an object $\ty$ such that
maps $B \to \ty$ correspond to _arbitrary_ maps $A \to B$. Let's specify
this notion better using the language of higher category theory:

A **subobject classifier** is a [[representing object|representable
functor]] for the functor $\rm{Sub} : \cE\op \to \Sets$ which takes an
object to its [[poset of subobjects]]. Since $\Sub(x)$ is a subcategory
of $\cE/x$, restricted to the objects which are (-1)-truncated, an
**object classifier** would be a representing object for $\cE/-$, the
functor which sends an object $X$ to the category of _arbitrary_
"$X$-indexed families", the [[slice category]] over $X$. If capturing
the directed structure isn't possible, then, at the very least, it
should represent $\rm{Core}(\cE/-)$ --- the [[core]] of $\cE$, so that
the isomorphisms between families are accurately represented.

However, there is an issue here: there is, a priori, an entire
*category* $\cE/x$, but only a *set* $\hom_{\cE}(x, U)$. Objects in a
category can have non-trivial isomorphisms, but there's no such notion
between elements in a set! Let's suppose that we had such an
equivalence, in the context $\cE = \Sets$, setting aside the _size_
issues for now: we have an object $U$ equipped with an isomorphism $r :
\hom(*, U) \cong \Sets/* \cong \Sets$. There's an element $b = r^{-1}(2)
: U$ classifying the type of booleans, which should have a non-trivial
identification $b = b$ corresponding to the involution on $2$. However,
this is not possible, since a set ([[by definition|set]]) only has
trivial identifications.

One might attempt to remedy the issue by looking for an object
classifier in a [[bicategory]], where $\hom(-, U)$ would be a genuine
category. However, this didn't actually fix anything, since we only
shifted the issue one level up: we now have an entire *bicategory*
$\cE/x$, which can't be classified by the mere *category* of maps
$\hom_{\cE}(-, U)$!

The issue does eventually resolve itself, if we're very persistent: if
we have an $\infty$-category $\cE$, where $\hom(-,-)$ can be a genuine
$\infty$-groupoid, then it's actually perfectly possible for there to be
an object $\ty$ with an isomorphism $\cE/- \cong \hom(-, \ty)$ --- well,
at least as long as we restrict ourselves to $\rm{Core}(\cE/-)$. We've
finally found a setting where object classifiers can exist: $\io$-categories!

Again, the importance of object classifiers is that they let us talk
about arbitrary objects as if they were points of an object $\ty$.
Specifically, any object $B$ has a _name_, a map $\ulcorner B \urcorner
: * \to \ty$, which represents the unique map $B \to *$. To make this
connection clearer, let's pass back to a syntactic presentation of type
theory, to see what universes look like "from the inside".

## Universes, internally

Inside type theory, object classifiers present themselves as types which
contain types, which we call **universes**. Every type is contained in
some universe, but it is not the case that there is a universe
containing all types; In fact, if we did have some magical universe
$\ty_\infty : \ty_\infty$, we could reproduce Russell's paradox, as is
done [here].

[here]: 1Lab.Counterexamples.Russell.html

The solution to this is the usual stratification of objects into
"sizes", with the collection of all "small" objects being "large", and
the collection of all "large" objects being "huge", etc. On the semantic
side, a $\io$-topos has a sequence of object classifiers for maps with
$\kappa$-compact fibres, where $\kappa$ is a regular cardinal;
Syntactically, this is reflected much more simply as having a _tower_ of
universes with $\ty_i : \ty_{1+i}$. So, in Agda, we have:

<!--
```
module _ where private
```
-->

```agda
  _ : Type
  _ = Nat

  _ : Type₁
  _ = Type
```

In Agda, we do not have automatically that a "small" object can be
considered a "large" object. When this is the case, we say that
universes are _cumulative_. Instead, we have an explicit
`Lift`{.Agda}ing construction that lets us treat types as being in
higher universes:

```agda
  _ : Type₂
  _ = Lift (lsuc (lsuc lzero)) Type
```

To avoid having `Lift`{.Agda} everywhere, universes are indexed by a
(small) type of countable ordinals, called `Level`, and constructions
can be parametrised by the level(s) of types they deal with. The
collection of all $\ell$-level types is $\ty_{\rm{lsuc}\ \ell}$, which
is itself a type in the next universe up, etc. Since levels are
themselves inhabitants of a type, we do in fact have a definable
function $\lambda \ell.\ \ty_\ell$. To avoid further Russellian
paradoxes, functions out of Level must be _very big_, so they live in
the "first infinite universe", $\ty_\omega$. There is another hierarchy
of infinite universes, with $\ty_{\omega+i}$ inhabiting
$\ty_{\omega+(1+i)}$. To avoid having even more towers of universes, you
can't quantify over the indices $i$ in $\ty_{\omega+i}$. To summarize,
we have:

$$
\ty : \ty_1 : \ty_2 : \cdots \ty_{\omega} : \ty_{\omega+1} : \ty_{\omega+2} : \cdots
$$

To represent a collection of types varying over an value of $A$, we use
a function type into a universe, called a **type family** for
convenience: A type family over $A$ is a function $A \to \ty_i$, for
some choice of level $i$. An example of a type family are the _finite
types_, regarded as a family $\rm{Fin} : \bb{N} \to \ty$ --- where
$\rm{Fin}(n)$ is a type with $n$ elements. Type families are also used
to model **type constructors**, which are familiar to programmers as
being the _generic types_. And finally, if we have a type $B : \ty_i$,
we can consider the **constant family** at $B$, defined to be the
function $\lambda (x : A).\ B$.

To cap off the correspondence between universes and object classifiers,
thus of type families and maps, we have a theorem stating that the space
of maps into $B$ is equivalent to the space of type families indexed by
$B$. As a reminder, you can click on the name `Fibration-equiv`{.Agda}
to be taken to the page where it is defined and explained.

```agda
  _ : ∀ {B : Type} → (Σ[ E ∈ Type ] (E → B)) ≃ (B → Type)
  _ = Fibration-equiv
```

## Universes and size issues

Perhaps one of the most famous paradoxes in the history of formal logic,
[Russell's paradox] reminds us that, for most reasonable kinds of
"collection" --- be they sets, types, or [categories] --- considering
_the collection of all collections that do not contain themselves_ is a
road that leads to madness. The standard way of getting around these
issues, at least in set-theoretic foundations as applied to category
theory, is to refer to such problematic collections as "[classes]", and to
only axiomatise the _sets_ which are not too big.

[classes]: https://ncatlab.org/nlab/show/proper+class

In the branches of mathematics that Alexander Grothendieck influenced, a
more common approach is to work instead with _Grothendieck universes_: A
Grothendieck universe is a set $\cU$ that forms a transitive model of
ZF, closed under $\cU$-small indexed products.  The classification of
models of ZF implies that any Grothendieck universe $\cU$ is
equivalent to a segment of the [von Neumann universe] $\bf{V}_\kappa$,
where $\kappa$ is a strongly inaccessible cardinal --- essentially, an
upper bound on the size of the sets in $\cU$.

[von Neumann universe]: https://en.wikipedia.org/wiki/Von_Neumann_universe

[Russell's paradox]: 1Lab.Counterexamples.Russell.html
[categories]: Cat.Base.html

In traditional mathematical writing, it is common to entirely ignore
size issues, save perhaps for an offhand mention of Grothendieck
universes (or strongly inaccessible cardinals) within the first few
sections. Working in a proof assistant forces us to be honest about the
size of our constructions: Correspondingly, we try to be precise in our
prose as well. As mentioned above, Agda universes are stratified into a
pair of hierarchies $\ty_\kappa$ and $\ty_{\omega+n}$, where we're using
$\kappa$ to stand for a variable of `Level`{.Agda} type. The
`Level`{.Agda} is a built-in type which contains a constant representing
$0$, is closed under taking successors, and is closed under taking
binary maxima.

We refer to structured type (e.g. a category, or a group) as
**$\kappa$-small** when its underlying type inhabits the $\kappa$th
universe; For the specific case of categories, we also use the
terminology **locally $\kappa$-small** to refer to the universe in which
the family $\hom(-,-)$ lands. We use subscript Greek letters in prose to
index our structures by their universe level. For example,
$\Sets_\kappa$ is the ($(1+\kappa)$-small, locally $\kappa$-small)
category of $\kappa$-small sets.

<details>
<summary>Small (hah!) note on small categories.</summary>

For those familiar with the notions of _internal_ and _enriched_
categories, we might rephrase the _classical_ definitions of
$\kappa$-small and locally $\kappa$-small categories as follows:

- A category $\cC$ is $\kappa$-small if it is an internal category in
$\Sets_\kappa$;

- A category $\cC$ is locally $\kappa$-small if it is enriched over
the Cartesian monoidal category $\Sets_\kappa$.

Because every type is contained in some universe, we note that _every_
category that appears in our development is locally $\kappa$-small for
_some_ universe level $\kappa$. In particular, we have no "type of
categories", but instead a type of "$\kappa$-small, locally
$\lambda$-small categories".

</details>

::: warning
Note that our use of the term "$\kappa$-small" is nonstandard. In
set-theoretic foundations, where the only objects are sets anyway, this
means "category internal to $\Sets_\kappa$", as mentioned in the infobox
above. In the 1Lab, the objects we manipulate are _higher groupoids_
rather than sets, and so very few categories will be internal to a
category of sets. Instead, when we describe a category $\cC$ is
$\kappa$-small, we mean that the type of objects of $\cC$ is an
inhabitant of the universe $\ty_\kappa$, and that the $\hom_\cC(-,-)$
family is valued in $\Sets_\kappa$. Our shorthand for the traditional
notion is a "**[strict] $\kappa$-small**" category.
:::

[strict]: Cat.Instances.StrictCat.html

<!--
```agda
_ : Type
_ = Level
```
-->

Our policy is to keep the use of universes "as precise as possible":
Definitions are polymorphic over as many levels as they can possibly be,
and they are always placed in the smallest universe in which they fit.
This is, however, an iterative process: For example, our definition of
"sheaf topos" was originally parametrised over 5 levels, but after
formalising more desirable properties of topoi, we have found that the
definition only really mentions two levels.

# Interlude: Basics of paths

Since the treatment of paths is the most important aspect of homotopy
type theory, rest assured that we'll talk about it in more detail later.
However, before discussing the dependent sum of a type family, we must
discuss the fundamentals of paths, so that the categorical/homotopical
connections can be made clear. Before we even get started, though, there
is something that needs to be made very clear:

<div style="display: flex; flex-direction: column; align-items: center;">
<span style="font-size: 20pt">
_**Paths are not equality!**_
</span>
</div>

The only conceptualisation of paths that is accurate in all cases is
that types are $\infty$-groupoids, and hence path spaces are the
Hom-$\infty$-groupoids given by the structure of each type. However,
this understanding is very bulky, and doesn't actually help
understanding paths all that much --- so we present a bunch of other
analogies, with the caveat that they only hold for some types, or are
only one of the many possible interpretations of paths in those types.

The ideas presented below are grouped in blue `<details>` elements, but
not because they aren't important; You **should** read all of them.

<details>
<summary>
**Idea #1**: Some types behave like sets, providing an embedding of
"classical" equality behaviour into homotopy type theory. While these
types may not be as "exciting" as others, they aren't any less
important!
</summary>

Contradicting the big bold warning up there, **in a very restricted
class of types**, paths _do_ behave like the equality relation! We call
these types **[[sets]]**, and their defining property is that they "only
have identity paths" --- hence they could also be called "discrete
types", by analogy with "[[discrete category]]", but this terminology is
not employed because "discrete" already has a distinct type-theoretic
meaning.[^deceq]

Types in this class include the [[natural numbers]], the [[integers]],
the rationals and the reals; Also included is every [[finite type]], and
the [[power set]] of any type at all. The type of functions $A \to B$,
where $B$ is a set, is again a set. We can generalise this and say that
"most" type formers preserve set-ness.

Note that the meaning of "is a set"/"is not a set" in HoTT is distinct
from how that sentence is used in classical mathematics, where a
collection _is a set_ if it's definable in the language of whatever
foundational system you're using. For example, in ZFC, the collection
of all sets is not a set --- because if it were, we could reproduce
Russell's paradox.

In HoTT, being a set has to do with _spatial_ structure: a set has
only trivial paths. Examples of non-sets would then be given by types
that have interesting paths, like the circle, which has a non-trivial
loop. Coincidentally, the type of all sets is _not_ a set, since its
spatial structure is given by the _isomorphisms_ of sets --- and sets
can have non-trivial automorphism groups.

</details>

[^deceq]: _Discreteness_, type-theoretically, has to do with whether we
can decide equality in that type by an algorithm. For example, the
natural numbers are discrete, because we can compare the numerals they
represent in time bounded by the size of the number. On the other hand,
sequences of natural numbers are not discrete, because an algorithm can
not run forever. Any discrete type is a set, and assuming excluded
middle, any set is discrete.

<details>
<summary>
**Idea #2**: Some types are best understood as representing spaces, with
intrinsic homotopic information, which we can investigate using
type-theoretic methods. This interpretation is the core idea of
"synthetic homotopy theory", a whole field of maths!
</summary>

We conceptualise some types (like the circle mentioned above) as being
representatives for spaces, though this does not mean that they have any
intrinsically-detectable _topology_ in the sense of "open
sets"-topological spaces. Instead, we think of these types as being an
incarnation of spaces _à la_ homotopy theory, with structure similar to
what you'd find there: Homology groups, cohomology groups, but most
easily seen are the homotopy groups. In these types, type-theoretic
paths quack like topological paths.

Indeed, any type in homotopy type theory has an associated sequence of
homotopy groups, and these behave precisely like the homotopy groups
of classical algebraic topology --- with the difference that the way
we compute them in HoTT has a distinctly more "typey" flavour.

This interpretation of types as spaces leads us to look at the
statement "there is a type $X$ with $\pi_1(X) \cong \bb{Z}$" and
rightly call $X$ "the [[circle]]", even though a topologist might object
that our circle is not any subset of $\bb{R}^2$. Similarly, we
might take the integer $2$ and apply the isomorphism above, to get a
path in $X$ which "walks clockwise around the circle twice".

</details>

<details>
<summary>
**Idea #3**: HoTT provides a setting for doing category theory where all
constructions are intrinsically isomorphism-invariant. Under this light,
types provide the _underlying groupoids_ of categories.
</summary>

When doing category theory in HoTT, we have some types that naturally
arise as the type of objects in a category, such as the type of groups
relative to a universe. In category theory done set-theoretically, the
collection of objects in $C$ has two _different_ notions of sameness:
The set-theoretic equality $a = b$, with behaviour given by the axiom of
extensionality and divorced from the categorical structure, and the
class of _isomorphisms_ of $C$, $a \cong b$, which naturally has to do
with the categorical structure.

A big part of doing category theory in set-theoretic foundations is
learning in which situations we should talk about the set-theoretic
equality of objects, and when we should talk about isomorphism ---
what you end up discovering is that constructions that talk about
equality of objects should be done very sparingly, so much so that
they're colloquially called "evil".

Conversely, the possibility of talking about equality of objects at
all means that we have to spend effort verifying that constructions
appropriately respect isomorphisms, though of course this verification
can be (and often ends up being) handwaved.

In HoTT, we can do better: We add a condition to the definition of
category that says the paths of the type of objects _must_ correspond to
the categorical isomorphisms --- which we call "univalence". While this
condition might initially seem hard to fulfill, it's surprisingly common
to come by [[univalent categories]], since most constructions on categories
preserve univalence! For instance:

* If $A$ and $B$ are univalent categories, then so is the
  [[product|product category]] $A \times B$ and the disjoint union $A
  \uplus B$; The initial and [[terminal categories]] are trivially
  univalent.

* If $C$ is a univalent category, then so is the [[slice category]]
  $C/c$, and the coslice $c/C$. More general [[comma categories]] are
  [[also univalent|univalence of comma category]].

* If $C$ is a univalent category, then for any $D$, so is the [[functor
  category]] $[D,C]$; This implies that a very large class of categories
  is univalent, e.g. the models of any Lawvere theory in a univalent
  category.

  Further, since $\Sets$ is a univalent category, the Yoneda lemma
  implies that every $C$ can be embedded into a univalent category - the
  functor category $[C\op,\Sets]$. If we restrict to the subcategory of
  representable presheaves, we have that every $C$ admits a [[full|full
  functor]], [[faithful|faithful functor]] and [[essentially
  surjective]] functor into a univalent category, called the [[Rezk
  completion]] of $C$; If $C$ was already univalent, this functor is an
  equivalence.

In addition to the benefit of univalent categories that will be
presented outside the fold, they're also interesting in their own right
because they are better constructively behaved than categories with a
set of objects: For instance, in the last bullet point above we appealed
to the statement "every [[fully faithful]], [[essentially surjective]] functor
is an equivalence". For univalent categories, this is a theorem without
any form of choice axiom!

</details>

One benefit that HoTT brings to the table is that it very naturally
leads to mixing and matching the interpretations above. For example, the
underlying groupoid of a univalent category can just as well be
interpreted as a space, mixing interpretations #2 and #3. The spatial
interpretation of categories really shines when we pass to higher
categories, where the notion of "unique" behaves very badly.

When thinking $n$-categorically, even for small values of $n$, one must
first weaken "unique" to "unique up to unique isomorphism", and then to
something like "unique up to isomorphism, which is unique up to unique
invertible 2-cell". Reasoning spatially, we see that "unique up to
isomorphism" really means that there is a _contractible space_ of
choices for that object --- a notion which is well-behaved at any level
of higher categorical complexity.

Every type $A$ has an associated family of path types --- to form a path
type, we must have two inhabitants of $A$ handy, called the _endpoints_.
The type of paths between $x$ and $y$ in $A$ is written $x \equiv_A y$,
where the subscript $A$ is omitted when it can be inferred from context.
The name _path_ is meant to evoke the topological idea of path, after
which the paths in cubical type theory were modelled. In topology, a
path is defined to be a _continuous function_ from the real unit
interval $[0,1] \to X$, so that we can interpret a path as being a point
"continuously varying over time".

It would be incredibly difficult (and oversized!) to formalise the
entire real line and its topology to talk about paths, which are meant
to be a fundamental concept in type theory, so we don't bother! Instead,
we look at which properties of the unit interval $[0,1]$ give paths
their nice behaviour, and only add those properties to our type theory.
The topological interval is **contractible**, and it has two **endpoint
inclusions**, with domain the one-point space. Those are the properties
that characterise it (for defining paths), so those are the properties
we keep!

The **interval type**, $\bb{I}$, has two introduction rules --- but
they are so simple that we refer to them as "closed inhabitants"
instead. These are written $\rm{i0}$ and $\rm{i1}$, and they denote the
left- and right- hand side of the unit interval. A classic result in the
interpretation of constructive mathematics says that any function
defined inside type theory is automatically continuous, and so, we
define the type $x \equiv_A y$ to be the type of functions $f :
\bb{I} \to A$, restricted to those where $f(\rm{i0}) = x$ and
$f(\rm{i1}) = y$ _definitionally_.

The introduction rule for paths says that if $e : \bb{I} \to A$,
with $e(\rm{i0}) = x$ and $e(\rm{i1}) = y$ (those are _definitional_
equalities), then we can treat it as a path $x \equiv_A y$. Conversely,
if we have a term $p : x \equiv_A y$, then we can apply it to an
argument $i : \bb{I}$ to get a term $p(i)$ of type $A$. The type of
paths satisfies the same reduction rule ($\beta$-reduction) as function
types, but with an additional rule that says $p(\rm{i0})$ is
definitionally equal to $x$ (resp. $\rm{i1}$ and $y$), even if $p$ has
not reduced to a $\lambda$-abstraction.

By considering the constant function at a point $x : A$, we obtain a
term $(\lambda i.\ x)$ of type $x \equiv_A x$, called the trivial path,
and referred to (for historical reasons) as `refl`{.Agda}, since for the
types that are sets, it expresses *refl*exivity of equality. In the
interpretation of types as $\infty$-groupoids, `refl`{.Agda} is the
identity morphism. The rest of the groupoid structure is here too! Any
path $p : x \equiv y$ has an inverse $p^{-1} : y \equiv x$, and for any
$p : x \equiv_A y$ and $q : y \equiv_A z$, there is a composite path $p
\bullet q : x \equiv_A z$. There are paths between paths which express
the groupoid identities (e.g. $p \bullet p^{-1} \equiv \refl$),
and those paths satisfy their own identities (up to a path between paths
between paths), and so on.

This little introduction to paths was written so that we can make some
of the ideas in the following section, about dependent sums, precise.
It's not meant to be a comprehensive treatment of the path type; For
that, see the section _[Paths, in detail]_ later on.

# Sums

Recall that in the construction of a map into $B$ from a predicate
$\chi : B \to \Omega$, we interpreted $\chi$ as a family of sets with at
most one element, and then took the disjoint union of that family,
written $\sum_{(x : B)} \chi(x)$, which admits a _projection_ onto $B$.
That was actually a sneaky introduction of the dependent sum type
former, $\sum$! Indeed, the short discussion there also made some
mention of the introduction rule, but let's reiterate with more clarity
here.

If we have some index type $A : \ty_\ell$, and a family of types $B \to
\ty_{\ell'}$, then we can form the **dependent sum type** $\sum_{(x
: A)} B$. When the index is clear from context, we let ourselves omit
the variable, and write $\sum B$. Since $\sum B$ is a type, it lives in
a universe; Since it admits a projection onto $A$ and a projection onto
a fibre of $B$, it must be a universe bigger than both $\ell$ and
$\ell'$, but it need not be any bigger: The dependent sum of $B$ lives
in the universe indexed by ${\ell \sqcup \ell'}$.

The introduction rule for $\sum B$ says that if you have an $a : A$, and
a $b : B(a)$, then the pair $(a,b)$ inhabits the type $\sum B$. Thus the
inhabitants of the dependent sum are ordered pairs, but where the second
coordinate has a type which _depends on the value_ of the first
coordinate. If we take $B$ to be a constant type family, we recover a
type of ordered pairs, which we call the **product** of $A$ and $B$,
which is notated by $A \times B$.

For the elimination rules, well, pairs would be rather useless if we
couldn't somehow get out what we put in, right? The first elimination
rule says that if we have an inhabitant $e : \sum_{(x : A)} B(x)$, then
we can project out the first component, which is written $e \rm{.fst}$,
to get an inhabitant of $A$. The computation rule here says that if you
project from a pair, you get back what you put in: $(a,b)\rm{.fst} = a$.

Projecting out the second component is trickier, so we start by
considering the special case where we're projecting from a literal pair.
We know that in $(a,b)$, the terms have types $a : A$ and $b : B(a)$, so
in this case, the second projection is $(a,b)\rm{.snd} : B(a)$. When
we're not projecting from a literal pair, though, we're in a bit of a
pickle. How do we state the type of the second projection, when we don't
know what the first component is? Well - we generalise. We know that for
a pair, $a = (a,b)\rm{.fst}$, so that we may replace the aforementioned
typing for $\rm{.snd}$ with the wordy $(a,b)\rm{.snd} :
B((a,b)\rm{.fst})$. Now we don't use any subterms of the pair in the
typing judgement, so we can generalise:

$$
e\rm{.snd} : B (e\rm{.fst})
$$

A very common application of the dependent sum type is describing types
equipped with some _structure_. Let's see an example, now turning to
Agda so that we may see how the dependent sum is notated in the
formalisation.  We define a _pointed magma structure_ on a type to be a
point of that type, and a binary function on that type. If we let the
type _vary_, then we get a type family of pointed magma structures:

<!--
```agda
module _ where private
```
-->

```agda
  Pointed-magma-on : Type → Type
  Pointed-magma-on A = A × (A → A → A)
```

Taking the dependent sum of this family gives us the type of pointed
magmas, where inhabitants can be described as triples $(T,i,m)$ where $T
: \ty$ is the _underlying type_, $i : T$ is the distinguished point, and
$m : T \to T \to T$ is the binary operation. Note that, to be entirely
precise, the pair would have to be written $(T,(i,m))$, but since by far
the most common of nested pairs is with the nesting on the right, we
allow ourselves to omit the inner parentheses in this case.

```agda
  Pointed-magma : Type₁
  Pointed-magma = Σ Type Pointed-magma-on
```

Note that, since we fixed the family to $\ty \to \ty$, and recalling
that $\ty : \ty_1$ are the first two universes, the type of all pointed
magmas in $\ty$ lives in the next universe, $\ty_1$. If the type of all
pointed magmas were in $\ty$, then we could _again_ reproduce Russell's
paradox.

Just like functions, pairs enjoy a uniqueness principle, which (since
coming up with names is very hard), also goes by $\eta$-expansion. The
rule says that every inhabitant of a $\Sigma$-type is _definitionally_
equal to the pairing of its projections: $p = (p\rm{.fst},
p\rm{.snd})$. This essentially guarantees us that the inhabitants of
a dependent sum type can't have any "extra stuff" hiding from our
projection maps; They are exactly the pairs, no more, and no less.

The dependent sum is a construction that goes by many names. In addition
to the ones mentioned below (which are the names people actually use),
you _could_ call it _the Grothendieck construction_, denote it by $\int
B$, and have a hearty chuckle --- if it weren't for the fact that the
Grothendieck construction is generally taken for functors between
_categories_ rather than just groupoids.

* **$\mathbf{\Sigma}$-type**, named after its shape;

* **Disjoint union**, since if we take $A$ to be the 2-point type, then
the dependent sum $\sum B$ of $B : 2 → \ty$ is exactly the disjoint
union $B(0) \uplus B(1)$;

* Thinking homotopically, you can consider a type family $B : A \to \ty$
to be a _fibration_, since as we shall see later it satisfies the path
lifting property; In that sense, $\sum B$ gives the **total space**, and
the actual fibration is the first projection map $x \mapsto
x\rm{.fst}$.

This last correspondence will be particularly important later, and it
inspires much of the terminology we use in HoTT. Since universes are
object classifiers, we know that there is an equivalence between type
families $F : B \to \ty$ and maps into $B$.  Dependent sums and paths
let us be more precise about this equivalence: We can turn any type
family $F : B \to \ty$ into a map $\rm{fst} : \sum F \to B$, and looking
at the fibre of first over a point $y$ recovers $F(y)$. We thus blur
this distinction a bit and refer to $F(x)$ for some $x : B$ as a fibre
of $F$, and we say that something happens _fibrewise_ if it happens for
each $F(x)$.

One last thing to mention about $\Sigma$-types is that they are the
realization of general subsets. This is a special case of the idea of
stuff-with-structure, where the structure is merely a witness for the
truth of some predicate of the first value. For example, recall that we
defined the fibre of $f$ over $y$ as $\{ x \in A : f(x) = y \}$. In type
theory, this is rendered with a $\Sigma$-type, as below:

<!--
```
module _ {A B : Type} where private
```
-->

```agda
  fibre : (A → B) → B → Type
  fibre f y = Σ[ x ∈ A ] (f x ≡ y)
```

# Dependent products

Imagine that we have two types, $A$ and $B$. For simplicity, they live
in the same universe, which can be any universe of our choice. We know
that we can consider $B$ to be a constant type family taking indices in
$A$: $\lambda (x : A).\ B$. Furthermore, we know that the total space of
this family is the product type $A \times B$, and that it comes equipped
with a projection map $\rm{fst} : \sum B \to A$.

Given any function $f : A \to B$, we define its _graph_ $\rm{graph}(f) :
A \to A \times B$ to be the function $\lambda x.\ (x, f(x))$, which
takes each point of the input space to an ordered pair where the first
coordinate is the input, and the second coordinate is the output of $f$
_at that input_. The graph of a function is special because of its
interaction with the projection map $\rm{fst} : A \times B \to A$. In
particular, we can see that $\lambda x.\ \rm{graph}(f)\rm{.fst}$ is the
identity function! This property turns out to precisely characterise the
functions $A \to A \times B$ which are the graphs of functions $A \to
B$.

By rewriting the equality we noticed above in terms of function
composition, we obtain $\rm{.fst} \circ \rm{graph}(f) = \id$. A
function, like $\rm{graph}(f)$, which composes on the right with some
other function $\rm{fst}$ to give the identity function, is called a
**section** of $\rm{fst}$. This lets us characterise the functions $A
\to B$ as the _sections of $\rm{fst} : A \times B \to A$._ In this
sense, we see that a function $A \to B$ is precisely a choice of values
$f(x)$, where $f(x)$ is in the fibre over $x$ --- in this case, the
fibres over all points are $B$!

Given a map $g : A \to A \times B$ that we know is a section of
$\rm{fst}$, we can recover a function $f : A \to B$. Specifically, given
a point $x : A$, we know that the second projection $g(x)\rm{.snd}$ has
type $B$ --- so we can simply define $f$ to be $\lambda x.\
g(x)\rm{.snd}$. Since we know that $g$ is a section of $\rm{fst}$, we
conclude that $\rm{graph}(f) = g$.

This idea generalises cleanly from the case where $B$ is just some type,
to the case where $B$ is a type family indexed by $A$. We define a
**section of $B$** to be a function $g : A \to \sum B$, where
$\rm{fst} \circ g = \id$. Note that this terminology conflates the
type family $B$ with the projection map $\sum B \to A$, keeping with the
trend of identifying type families with fibrations.  Generalising the
argument from the previous paragraph, we show that a section $g$ gives a
rule for assigning a point in $B(x)$ to each point in $x$. We again take
the second projection of $g(x)\rm{.snd}$, but since now $B$ is a type
family, this lives in the type $B(g(x)\rm{.fst})$ --- but since we know
that $g$ is a section of $\rm{fst}$, we can correct this to be $B(x)$.

We would like to package up such a rule into a function $A \to B$, but
this is not a well-formed type, since $B$ is a type _family_. Moreover,
this would "forget" that $x$ is sent to the fibre $B(x)$. Thus, we
introduce a new type former, the **dependent product type**, written
$\prod_{(x : A)} B(x)$ or more directly $(x : A) \to B(x)$. The
inhabitants of this type are precisely the sections of $B$! More
importantly, the introduction, elimination, computation and uniqueness
rules of this type are exactly the same as for the [function
type](#functions).

The dependent product type takes on another very important role when
universes are involved: Supporting _polymorphism_. In programming, we
say that a function is polymorphic when it works uniformly over many
types; Dependent products where the index type is a universe reflect
this exactly. For example, using polymorphism, we can write out the
types of the first and second projection maps:

<!--
```agda
module _ where private
```
-->

```agda
  project-first : (A : Type) (B : A → Type) → Σ A B → A
  project-first A B x = x .fst

  project-second : (A : Type) (B : A → Type)
                 → (p : Σ A B) → B (project-first A B p)
  project-second A B x = x .snd
```

In the logical interpretation, the dependent product type implements the
universal quantifier $\forall$. For example (keep in mind that in
general, **we should not read path types as equality**), we could read
the type <nobr>$(x\ y : A) \to x \equiv y$</nobr> as the proposition
"for all pairs of points $x$ and $y$ of $A$, $x$ is equal to $y$".
However, an inhabitant of this type has a much more interesting
_topological_ interpretation!

<details open>
<summary>**Worked example**: Interpreting dependent sums as fibrations
and dependent products as sections lets us derive topological
interpretations for types. We show how to do this for the type $(x\ y :
A) \to x \equiv y$, and show that a space $A$ admitting an inhabitant of
this type has the property of "being contractible if it is inhabited".
</summary>

First, we'll shuffle the type so that we can phrase it in terms of a
single dependent product, and a single type family. We define a type $A$
to be a _subsingleton_ if there is a term

$$f : (xy : A \times A) \to (xy\rm{.fst} \equiv xy\rm{.snd})$$

An $f$ of this type can be seen as a section of the type family $F : A
\times A \to \ty$ defined by the rule

$$
F(x,y) \mapsto (x \equiv y)
$$

The total space $\sum F$ of this family is the space of all paths in
$A$, which will be written as $A^\bb{I}$ to emphasise its nature as
a path space. Since it is the total space of a type family, it comes
equipped with a fibration $\rm{fst} : A^\bb{I} \to A \times A$.
Given that a term in $A^\bb{I}$ can be seen to be a pair $((x, y),
p)$ where $p : x \equiv y$, we see that this fibration projects both
endpoints of a path --- so we will write it $(d_0,d_1) : A^\bb{I}
\to A \times A$, since it is the pairing of the maps which evaluate a
path at the left and right endpoints of the interval.

As a very quick aside, there is a map $r : \lambda x.\ (x, x, \refl$
making the diagram below commute. This diagram expresses that the
diagonal $A \to A \times A$ can be factored as a weak equivalence
followed by a fibration through $A^\bb{I}$, which is the defining
property of a _path space object_.
$A$.

$$
A \xrightarrow{\~r} A^\bb{I} \xrightarrow{(d0,d1)} \to A \times A
$$

A section of this fibration --- that is, a dependent function like $f$
--- is then a _continuous_ function $A \times A \to A^\bb{I}$, with
the property that $(d_0,d_1) \circ f = \id$. Now assume that our
space $A$ is pointed, say with a point $y_0 : A$, and that we have a
section $f$. We can then define the homotopy $(x,t) \mapsto f(x,y_0,t)$,
mapping between the identity function on $A$ and the constant
function at $y_0$, exhbiting the space $A$ as contractible.

If you assume the law of excluded middle, every space is either pointed
or empty. In this case, we can describe a space $A$ equipped with a map
like $f$ as being "either empty or contractible", but we prefer the
terminology "contractible if inhabited" or **subsingleton** instead.

</details>

# What next?

While the text above was meant to serve as a linearly-structured
introduction to the field of homotopy type theory, the rest of the 1Lab
is not organised like this. It's meant to be an _explorable_
presentation of HoTT, where concepts can be accessed in any order, and
everything is hyperlinked together. However, we can highlight the
following modules as being the "spine" of the development, since
everything depends on them, and they're roughly linearly ordered.

## Paths, in detail

```agda
open import 1Lab.Path
```

The module `1Lab.Path`{.Agda} develops the theory of path types, filling
in the details that were missing in _[Interlude - Basics of
paths](#interlude-basics-of-paths)_ above. In particular, the
Path module talks about the structure of the **interval type**
$\bb{I}$, the definition of **dependent paths**, **squares**, and
the symmetry involution on paths. It then introduce the **transport**
operation, turns a path between types into an equivalence of types.

It also exposits about the structure of types as Kan complices; In
particular, the Path module defines and talks about **partial
elements**, which generalise the notion of "horn of a simplex" to any
shape of partial cube; Then, it defines **extensibility**, which
exhibits a partial element as being a subshape of some specific cube,
and the **composition and filling** operations, which express that
extensibility is preserved along paths. Finally, it introduces the
**Cartesian coercion** operation, which generalises transport.

To reiterate, paths are _the most important idea in cubical type
theory_, so you should definitely read through this module!

## Equivalences

The idea of subsingleton type, mentioned in passing in the discussion
about universes and expanded upon in the section on dependent products,
generalises to give the notion of **h-level**, which measures how much
interesting homotopical information a type has. A h-level that comes up
very often is the level of **sets**, since these are the types where
equality behaves like a logical proposition. Due to their importance, we
provide a module defining equivalent characterisations of sets.

```agda
open import 1Lab.HLevel
```

Contractible types can be used to give a definition of equivalence that
is well-behaved in the context of higher category theory, but it is not
the only coherent notion. We also have half-adjoint equivalences and
bi-invertible maps. Finally, we have a module that explains why these
definitions are needed in place of the simpler notion of "isomorphism".

```agda
open import 1Lab.Equiv
open import 1Lab.Equiv.Biinv
open import 1Lab.Equiv.HalfAdjoint
open import 1Lab.Counterexamples.IsIso
```

## Univalence

```agda
open import 1Lab.Univalence
```

The module `1Lab.Univalence`{.Agda} defines and explains the **Glue**
type former, which serves as the Kan structure of the universe. It then
concretises this idea by describing how Glue can be used to turn any
equivalence into a path between types, which leads to a proof of the
**univalence principle**. After, we prove that the type of equivalences
satisfies the same induction principle as the type of paths, and that
universes are object classifiers.

```agda
open import 1Lab.Univalence.SIP
```

While univalence guarantees that equivalence _of types_ is equivalent to
paths _in types_, it does not say anything about types-with-structure,
like groups or posets. Fortunately, univalence implies the **structure
identity principle**, which characterises the paths in spaces of
"structured types" as being homomorphic equivalence.
