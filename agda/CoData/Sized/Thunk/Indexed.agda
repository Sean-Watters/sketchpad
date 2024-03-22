{-# OPTIONS --sized-types --cubical-compatible #-}
module CoData.Sized.Thunk.Indexed where

open import Size

 --todo : Do we want indexed sized sets, or sized indexed sets?
 --are they equivalent

-- todo : this is still just the normal, un-indexed thunk.
record Thunk {ℓ} (F : SizedSet ℓ) (i : Size) : Set ℓ where
  coinductive
  field force : {j : Size< i} → F j
open Thunk public
