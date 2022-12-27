```
module Cat.Order.Diagram where
```

# Diagrams in posets

The namespace `Cat.Order.Diagram` contains many _duplicated_ definitions
of diagrams --- things you could also find in `Cat.Diagram` if you were
to look --- but specialised for the poset case, to cut down on the
redundant data. For example: posets have meets, not products.

Each module also defines the equivalence between the posetal diagram
(e.g.  meets resp. joins) and its categorified (products resp.
coproducts).

The reason behind this duplication is the same as the one behind having
a definition for coproducts rather than using "products in $\ca{C}\op$":
First, having both cuts eliminates the arbitrary choice of what diagram
is more "canonical" (e.g. are ends defined, or are they the duals of
coends?); Second, having duality as a theorem increases our confidence
in both definitions, whereas having a single definition would
_duplicate_ potential problems; Third, and this is minor, but defining
diagrams by copatterns always has intuitive names.
