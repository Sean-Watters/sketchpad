{-# OPTIONS --safe --guardedness #-}
module Codata.CoListFinite where

mutual
  data CoList (X : Set) : Set where
    [] : CoList X
    _∷_ : X → CoList-step X → CoList X

  record CoList-step (X : Set) : Set where
    constructor step
    coinductive
    field
      force : CoList X
open CoList-step

------------------------------------------------

-- we can make finite colists:
three : ∀ {X} → X → CoList X
three x = x ∷ step (x ∷ step (x ∷ step []))

-- we can make infinite colists:
mutual
  omega : ∀ {X} → X → CoList X
  omega {X} x = x ∷ omega-step x

  omega-step : ∀ {X} → X → CoList-step X
  omega-step x .force = omega x

------------------------------------------------

-- The finite fragment:
data IsFinite {X : Set} : CoList X → Set where
  [] : IsFinite []
  _∷_ : ∀ (x : X)
      → {xs : CoList X} → IsFinite xs
      → IsFinite (x ∷ (step xs))

------------------------------------------------

-- `three` is finite
three-fin : ∀ {X} → (x : X) → IsFinite (three x)
three-fin x = x ∷ (x ∷ (x ∷ [])) -- C-c C-a solves this instantly

-- For bonus points prove `Σ[ xs ∈ CoList X ] (IsFinite xs) ≅ List X`
-- and then work happily on lists thereafter
