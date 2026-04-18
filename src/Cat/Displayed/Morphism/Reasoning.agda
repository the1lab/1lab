-- Helper module bundling `Cat.Displayed.Reasoning` and
-- `Cat.Displayed.Morphism`.
open import Cat.Displayed.Base
open import Cat.Base

import Cat.Displayed.Reasoning as Dr
import Cat.Displayed.Morphism as Dm

module Cat.Displayed.Morphism.Reasoning
  {oa ℓa oe ℓe} {A : Precategory oa ℓa} (ℰ : Displayed A oe ℓe)
  where
  open Dr ℰ public
  open Dm ℰ public
