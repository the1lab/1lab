<!--
```agda
open import Cat.Diagram.Coequaliser.RegularEpi
open import Cat.Diagram.Pullback.Properties
open import Cat.Functor.FullSubcategory
open import Cat.Diagram.Limit.Finite
open import Cat.Morphism.Orthogonal
open import Cat.Diagram.Equaliser
open import Cat.Diagram.Pullback
open import Cat.Diagram.Initial
open import Cat.Instances.Comma
open import Cat.Instances.Slice
open import Cat.Diagram.Image
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Morphism.StrongEpi {o ℓ} (C : Precategory o ℓ) where

open Cat.Reasoning C
```

A **strong epimorphism** is an epimorphism which is, additionally, left
[orthogonal] to every monomorphism. Unfolding that definition, for $f :
a \epi b$ to be a strong epimorphism means that, given $g : c \mono b$
any mono, and $u$, $v$ arbitrarily fit into a commutative diagram like

[orthogonal]: Cat.Morphism.Orthogonal.html

~~~{.quiver .tall-1}
\[\begin{tikzcd}
  a && b \\
  \\
  c && {d\text{,}}
  \arrow[two heads, "f", from=1-1, to=1-3]
  \arrow[hook, "g"', from=3-1, to=3-3]
  \arrow["u"', from=1-1, to=3-1]
  \arrow["v", from=1-3, to=3-3]
  \arrow[dashed, from=1-3, to=3-1]
\end{tikzcd}\]
~~~

there is a contractible space of maps $b \to c$ which make the two
triangles commute. In the particular case of strong epimorphisms, it
actually suffices to have _any_ lift: they are automatically unique.

```agda
is-strong-epi : ∀ {a b} → Hom a b → Type _
is-strong-epi f = is-epic f × ∀ {c d} (m : c ↪ d) → m⊥m C f (m .mor)

lifts→is-strong-epi
  : ∀ {a b} {f : Hom a b}
  → is-epic f
  → ( ∀ {c d} (m : c ↪ d) {u} {v} → v ∘ f ≡ m .mor ∘ u
    → Σ[ w ∈ Hom b c ] ((w ∘ f ≡ u) × (m .mor ∘ w ≡ v)))
  → is-strong-epi f
lifts→is-strong-epi epic lift-it = epic , λ {c} {d} mm sq →
  contr (lift-it mm sq) λ { (x , p , q) → Σ-prop-path (λ _ → hlevel 1)
    (mm .monic _ _ (sym (q ∙ sym (lift-it mm sq .snd .snd)))) }
```

<!--
```agda
abstract
  is-strong-epi-is-prop
    : ∀ {a b} (f : Hom a b) → is-prop (is-strong-epi f)
  is-strong-epi-is-prop f = hlevel!
```
-->

To see that the uniqueness needed for orthogonality against a
monomorphism is redundant, suppose you'd had two fillers $\alpha$,
$\beta$, as in

~~~{.quiver .tall-1}
\[\begin{tikzcd}
  a && b \\
  \\
  c && {d\text{.}}
  \arrow["\alpha"', shift right=1, from=1-3, to=3-1]
  \arrow[two heads, "f", from=1-1, to=1-3]
  \arrow[hook, "g"', from=3-1, to=3-3]
  \arrow["u", from=1-1, to=3-1]
  \arrow["v", from=1-3, to=3-3]
  \arrow["\beta", shift left=1, from=1-3, to=3-1]
\end{tikzcd}\]
~~~

Since $g$ is a monomorphism, it suffices to have $g\alpha = g\beta$, but
by commutativity of the lower triangles we have $g\alpha = u = g\beta$.

## Properties

The proofs here are transcribed from [@Borceux:vol1, §4.3]. Strong
epimorphisms are closed under composition, for suppose that $f$ and $g$
are strong epics, and $m$ is the monomorphism to lift against. Fit them
in a skewed commutative _rectangle_ like

~~~{.quiver .tall-1}
\[\begin{tikzcd}
  a && b && c \\
  \\
  d &&&& e
  \arrow["g", two heads, from=1-1, to=1-3]
  \arrow["f", two heads, from=1-3, to=1-5]
  \arrow["u"', from=1-1, to=3-1]
  \arrow["z"', hook, from=3-1, to=3-5]
  \arrow["v", from=1-5, to=3-5]
  \arrow["w"{description}, dashed, from=1-3, to=3-1]
  \arrow["t"{description}, dashed, from=1-5, to=3-1]
\end{tikzcd}\]
~~~

By considering most of the right half as a single, weirdly-shaped square
(the $vfg = zu$ commutative "square"), we get an intermediate lift $w :
b \to d$ such that $wg = u$ and $zw=vf$ --- such that $z$, $w$, $f$, and
$v$ organise into the faces of a lifting diagram, too$ Since $f$ is a
strong epic, we have a _second_ lift $t : c \to d$, now satisfying
$tf=w$ and $zt=v$. A quick calculation, implicit in the diagram, shows
that $t$ is precisely the lift for $fg$ against $z$.

```agda
strong-epi-compose
  : ∀ {a b c} (g : Hom a b) (f : Hom b c)
  → is-strong-epi g
  → is-strong-epi f
  → is-strong-epi (f ∘ g)
strong-epi-compose g f (g-e , g-s) (f-e , f-s) =
  lifts→is-strong-epi epi fg-s
  where
  epi : is-epic (f ∘ g)
  epi α β p = f-e α β $ g-e (α ∘ f) (β ∘ f) $
    sym (assoc _ _ _) ·· p ·· assoc _ _ _
  fg-s : ∀ {c d} (m : c ↪ d) {u v} → v ∘ f ∘ g ≡ m .mor ∘ u → _
  fg-s z {u} {v} vfg=zu =
    let
      (w , wg=u , zw=vf) = g-s z (sym (assoc _ _ _) ∙ vfg=zu) .centre
      (t , tf=w , zt=v)  = f-s z (sym zw=vf) .centre
    in t , pulll tf=w ∙ wg=u , zt=v
```

Additionally, there is a partial converse to this result: If the
composite $gf$ is a strong epi, then $g$ is, too! Still thinking of the
same diagram, suppose the whole diagram is a strong epi, and you're
given $zw = vf$ to lift $f$ against $z$. We don't have a $u$ as before,
but we can take $u = wg$ to get a lift $t$.

```agda
strong-epi-cancel-l
  : ∀ {a b c} (f : Hom b c) (g : Hom a b)
  → is-strong-epi (f ∘ g)
  → is-strong-epi f
strong-epi-cancel-l g f (gf-epi , gf-str) = lifts→is-strong-epi epi lifts where
  epi : is-epic g
  epi α β p = gf-epi α β (extendl p)

  lifts : ∀ {c d} (m : c ↪ d) {u} {v} → v ∘ g ≡ m .mor ∘ u → _
  lifts {α} {β} mm {u} {v} sq = lifted .fst , lemma , lifted .snd .snd where
    lifted = gf-str mm {u = u ∘ f} {v = v} (extendl sq) .centre
    lemma = mm .monic _ _ (pulll (lifted .snd .snd) ∙ sq)
```

As an immediate consequence of the definition, a monic strong epi is an
isomorphism. This is because, being left orthogonal to all monos, it'd
be, in particular, left orthogonal to _itself_, and the only
self-orthogonal maps are isos.

```agda
strong-epi-mono→is-invertible
  : ∀ {a b} {f : Hom a b} → is-monic f → is-strong-epi f → is-invertible f
strong-epi-mono→is-invertible mono (_ , epi) =
  self-orthogonal→is-iso C _ (epi (record { monic = mono }))
```

# Regular epis are strong

Suppose that $f : a \to b$ is a regular epimorphism, that is, it
identifies $b$ as some quotient of $a$ --- the stuff of $b$ is that of
$a$, but with new potential identifications thrown in. Since we're
taking "strong epimorphism" as the definition of "well-behaved
epimorphism", we'd certainly like regular epis to be strong epis!

[regular epimorphism]: Cat.Diagram.Coequaliser.RegularEpi.html

This is fortunately the case. Suppose that $f : a \to b$ is the
coequaliser of some maps $s, t : r \to a$^[If you care, $r$ is for
"relation" --- the intuition is that $r$ specifies the _relations_
imposed on $a$ to get $b$], and that $z : c \mono b$ is a monomorphism
we want to lift against.

~~~{.quiver .tall-1}
\[\begin{tikzcd}
  r & a && b \\
  \\
  & c && d
  \arrow["s", shift left=1, from=1-1, to=1-2]
  \arrow["t"', shift right=1, from=1-1, to=1-2]
  \arrow["f", two heads, from=1-2, to=1-4]
  \arrow["z"', hook, from=3-2, to=3-4]
  \arrow["v", from=1-4, to=3-4]
  \arrow["u"', from=1-2, to=3-2]
  \arrow[dashed, from=1-4, to=3-2]
\end{tikzcd}\]
~~~

By the universal property of a coequaliser, to "slide $u$ over" to a map
$b \to c$, it suffices to show that it also coequalises the pair $s, t$,
i.e. that $us = ut$. Since $z$ is a mono, it'll suffice to show that
$zus = zut$, but note that $zu = vf$ since the square commutes. Then we
have

$$
zus = vfs = vft = zut{\text{,}}
$$

so there is a map $m : b \to c$ such that $mf = u$ --- that's
commutativity of the top triangle handled. For the bottom triangle,
since $f$ is a regular epic (thus an epic), to show $zm = v$, it'll
suffice to show that $zmf = vf$. But $vf = zu$ by assumption, and $mf =
u$ by the universal property! We're done.

```agda
is-regular-epi→is-strong-epi
  : ∀ {a b} (f : Hom a b)
  → is-regular-epi C f
  → is-strong-epi f
is-regular-epi→is-strong-epi {a} {b} f regular =
  lifts→is-strong-epi
    r.is-regular-epi→is-epic
    (λ m x → map m x , r.factors , lemma m x)
    where
    module r = is-regular-epi regular renaming (arr₁ to s ; arr₂ to t)
    module _ {c} {d} (z : c ↪ d) {u} {v} (vf=zu : v ∘ f ≡ z .mor ∘ u) where
      module z = _↪_ z
      map : Hom b c
      map = r.universal {e' = u} $ z.monic _ _ $
        z .mor ∘ u ∘ r.s ≡⟨ extendl (sym vf=zu) ⟩
        v ∘ f ∘ r.s      ≡⟨ refl⟩∘⟨ r.coequal ⟩
        v ∘ f ∘ r.t      ≡˘⟨ extendl (sym vf=zu) ⟩
        z .mor ∘ u ∘ r.t ∎
      lemma = r.is-regular-epi→is-epic _ _ $
        sym (vf=zu ∙ pushr (sym r.factors))
```

# Images

Now we come to the _raison d'être_ for strong epimorphisms: [[Images]].
The definition of image we use is very complicated, and the
justification is already present there, but the short of it is that the
image of a morphism $f : a \to b$ is a monomorphism $\im(f) \mono b$ which is
universal amongst those through which $f$ factors.

Since images have a universal property, and one involving [comma
categories] of [slice categories] at that, they are tricky to come by.
However, in the case where we factor $f : a \to b$ as

[comma categories]: Cat.Instances.Comma.html
[slice categories]: Cat.Instances.Slice.html

$$
a \xepi{\~f} \im(f) \mono b\text{,}
$$

and the epimorphism is _strong_, then we automatically have an image
factorisation of $f$ on our hands!

```agda
strong-epi-mono→image
  : ∀ {a b im} (f : Hom a b)
  → (a→im : Hom a im) → is-strong-epi a→im
  → (im→b : Hom im b) → is-monic im→b
  → im→b ∘ a→im ≡ f
  → Image C f
strong-epi-mono→image f a→im (_ , str-epi) im→b mono fact = go where
  open Initial
  open /-Obj
  open /-Hom
  open ↓Obj
  open ↓Hom

  obj : ↓Obj (Const (cut f)) (Forget-full-subcat {P = is-monic ⊙ map})
  obj .x = tt
  obj .y = restrict (cut im→b) mono
  obj .map = record { map = a→im ; commutes = fact }
```

Actually, for an image factorisation, we don't need that $a \epi \im(f)$
be an epimorphism --- we just need it to be orthogonal to every
monomorphism. This turns out to be precisely the data of being initial
in the relevant comma categories.

```agda
  go : Image C f
  go .bot = obj
  go .has⊥ other = contr dh unique where
    module o = ↓Obj other

    the-lifting =
      str-epi
        (record { monic = o.y .witness })
        {u = o.map .map}
        {v = im→b} (sym (o.map .commutes ∙ sym fact))

    dh : ↓Hom (Const (cut f)) _ obj other
    dh .α = tt
    dh .β .map = the-lifting .centre .fst
    dh .β .commutes = the-lifting .centre .snd .snd
    dh .sq = ext (idr _ ∙ sym (the-lifting .centre .snd .fst))

    unique : ∀ om → dh ≡ om
    unique om = ↓Hom-path _ _ refl $ ext $ ap fst $ the-lifting .paths $
      om .β .map , sym (ap map (om .sq)) ∙ idr _ , om .β .commutes
```

# In the lex case

Suppose that $\cC$ is additionally left exact, or more restrictively,
that it has all equalisers. In that case, a map left orthogonal to all
monomorphisms is _automatically_ an epimorphism, thus a strong epi.
Let's see how. First, there's a quick observation to be made about
epimorphisms: if $f$ is such that there exists a $g$ with $fg =
\id$, then $f$ is an epimorphism. You can think of this as a special
case of "$fg$ epic implies $f$ epic" or as a short calculation:

```agda
retract-is-epi
  : ∀ {a b} {f : Hom a b} {g : Hom b a}
  → f ∘ g ≡ id
  → is-epic f
retract-is-epi {f = f} {g} p α β q =
  α         ≡⟨ intror p ⟩
  α ∘ f ∘ g ≡⟨ extendl q ⟩
  β ∘ f ∘ g ≡⟨ elimr p ⟩
  β         ∎
```

We already know that if lifts exist and the map is epic, then it's a
strong epi, so let's assume that lifts exist --- we'll have no need for
uniqueness, here. Given $u, v$ and $uf = vf$ to lift against, form their
equaliser $Eq(u,v)$ and arrange them like

~~~{.quiver .tall-1}
\[\begin{tikzcd}
  a && b && x \\
  \\
  {Eq(u,v)} && b
  \arrow["f", from=1-1, to=1-3]
  \arrow["{\mathrm{id}}", from=1-3, to=3-3]
  \arrow["e"', hook, from=3-1, to=3-3]
  \arrow["{\exists!}"', from=1-1, to=3-1]
  \arrow["u", shift left=1, from=1-3, to=1-5]
  \arrow["v"', shift right=1, from=1-3, to=1-5]
  \arrow["w", dashed, from=1-3, to=3-1]
\end{tikzcd}\]
~~~

```agda
equaliser-lifts→is-strong-epi
  : ∀ {a b} {f : Hom a b}
  → (∀ {a b} (f g : Hom a b) → Equaliser C f g)
  → ( ∀ {c d} (m : c ↪ d) {u} {v} → v ∘ f ≡ m .mor ∘ u
    → Σ[ w ∈ Hom b c ] ((w ∘ f ≡ u) × (m .mor ∘ w ≡ v)))
  → is-strong-epi f
equaliser-lifts→is-strong-epi {f = f} eqs ls = lifts→is-strong-epi epi ls where
```

By the universal property of $Eq(u,v)$, since there's $uf = vf$, there's
a unique map $k : a \to Eq(u,v)$ such that $ek = f$. Arranging $k$, $f$,
$e$ and the identity(!) into a lifting square like the one above, we
conclude the existence of a dotted map $w$ satisfying, most importantly,
$ew = \mathrm{id}$ --- so that $e$, being a retract, is an epimorphism.

```agda
  epi : is-epic f
  epi u v uf=vf =
    let
      module ker = Equaliser (eqs u v)
      k = ker.universal uf=vf
      (w , p , q) = ls
        (record { monic = is-equaliser→is-monic C _ ker.has-is-eq })
        {u = k} {v = id}
        (idl _ ∙ sym ker.factors)
      e-epi : is-epic ker.equ
      e-epi = retract-is-epi q
```

Now, $e : Eq(u,v) \to B$ is the universal map which equalises $u$ and
$v$ --- so that we have $ue = ve$, and since we've _just_ shown that $e$
is epic, this means we have $u = v$ --- exactly what we wanted!

```agda
    in e-epi u v ker.equal
```

## Extremal epimorphisms

Another well-behaved subclass of epimorphism are the **extremal**
epimorphisms: An epimorphism $e : A \epi B$ is extremal if when, given a
factorisation $e = mg$ through a monomorphism $m : C \mono B$, then $m$
is an isomorphism. In a [[finitely complete category]], every extremal
epimorphism is strong; the converse is immediate.

```agda
is-extremal-epi→is-strong-epi
  : ∀ {a b} {e : Hom a b}
  → Finitely-complete C
  → (∀ {c} (m : c ↪ b) (g : Hom a c) → e ≡ m .mor ∘ g → is-invertible (m .mor))
  → is-strong-epi e
is-extremal-epi→is-strong-epi {a} {b} {e} lex extremal =
  equaliser-lifts→is-strong-epi lex.equalisers λ w → Mk.the-lift w where
    module lex = Finitely-complete lex
```

We adapt the proof from [@Borceux:vol1; §4.3.7]. After
`equaliser-lifts→is-strong-epi`{.Agda}, it will suffice to construct
_some_ lift for a square with $ve = mu$, with $m$ monic. Pull $v$ back
along $m$ to obtain the square

~~~{.quiver}
\[\begin{tikzcd}
  A \\
  \\
  && {A \times_D B} && B \\
  \\
  && C && D
  \arrow["m"', hook, from=5-3, to=5-5]
  \arrow["v", from=3-5, to=5-5]
  \arrow["q", hook, from=3-3, to=3-5]
  \arrow[from=3-3, to=5-3]
  \arrow["{\exists!\ r}", dashed, from=1-1, to=3-3]
  \arrow["e", curve={height=-12pt}, from=1-1, to=3-5]
  \arrow["u", curve={height=12pt}, from=1-1, to=5-3]
\end{tikzcd}\]
~~~

and obtain the unique factorisation $A \to A \times_D B$. Note that the
map $u : A \times_D B \mono B$ is a monomorphism since it results from
pulling back a monomorphism.

```agda
    module Mk {c d : Ob} (m : c ↪ d) {u : Hom a c} {v : Hom b d}
              (wit : v ∘ e ≡ m .mor ∘ u) where
      module P = Pullback (lex.pullbacks v (m .mor)) renaming (p₁ to q ; p₂ to p)
      r : Hom a P.apex
      r = P.universal {p₁' = e} {p₂' = u} wit

      abstract
        q-mono : is-monic P.q
        q-mono = is-monic→pullback-is-monic (m .monic) (rotate-pullback P.has-is-pb)
```

We thus have a factorisation $e = qr$ of $e$ through a monomorphism $q$,
which since $e$ was assumed extremal, must be an isomorphism. We define
the diagonal map $b \to c$ to be $pq^{-1}$ and compute that it commutes
appropriately:

```agda
      q-iso : is-invertible P.q
      q-iso = extremal record{ monic = q-mono } r (sym P.p₁∘universal)

      q⁻¹ = q-iso .is-invertible.inv

      the-lift : Σ (Hom b c) λ w → (w ∘ e ≡ u) × (m .mor ∘ w ≡ v)
      the-lift .fst = P.p ∘ q⁻¹
      the-lift .snd .fst = m .monic _ _ $
        m .mor ∘ (P.p ∘ q⁻¹) ∘ e ≡⟨ extendl (pulll (sym P.square)) ⟩
        (v ∘ P.q) ∘ q⁻¹ ∘ e      ≡⟨ cancel-inner (q-iso .is-invertible.invl) ⟩
        v ∘ e                    ≡⟨ wit ⟩
        m .mor ∘ u               ∎
      the-lift .snd .snd = invertible→epic q-iso _ _ $
        (m .mor ∘ (P.p ∘ q⁻¹)) ∘ P.q ≡⟨ pullr (cancelr (q-iso .is-invertible.invr)) ⟩
        m .mor ∘ P.p                 ≡˘⟨ P.square ⟩
        v ∘ P.q                      ∎
```

<!--
```agda
is-strong-epi→is-extremal-epi
  : ∀ {a b} {e : Hom a b}
  → is-strong-epi e
  → ∀ {c} (m : c ↪ b) (g : Hom a c) → e ≡ m .mor ∘ g → is-invertible (m .mor)
is-strong-epi→is-extremal-epi (s , ortho) m g p =
  make-invertible (inv' .centre .fst) (inv' .centre .snd .snd)
    (m .monic _ _ (pulll (inv' .centre .snd .snd) ∙ id-comm-sym))
  where
  inv' = ortho m (idl _ ∙ p)
```
-->
