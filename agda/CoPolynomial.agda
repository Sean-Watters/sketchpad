{-# OPTIONS --safe --guardedness #-}

-- Experiments on greatest fixpoints of copolynomial functors.
module CoPolynomial where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Sum
open import Data.Product

-- Presentation from UALib,
module Poly where
  data Poly : Set₁ where
    Id : Poly
    Const : Set → Poly
    _⊕_ : Poly → Poly → Poly
    _⊗_ : Poly → Poly → Poly

  ⟦_⟧ : Poly → Set → Set
  ⟦ Id ⟧ X = X
  ⟦ Const C ⟧ X = C
  ⟦ F ⊕ G ⟧ X = (⟦ F ⟧ X) ⊎ (⟦ G ⟧ X)
  ⟦ F ⊗ G ⟧ X = (⟦ F ⟧ X) × (⟦ G ⟧ X)

  data μ_ (F : Poly) : Set where
    inn : ⟦ F ⟧ (μ F) → μ F


---------------------

CoPoly : Set₁
CoPoly = {!!}

open import Data.Nat

record Test : Set where
  coinductive
  field
    A : ℕ
    B : ℕ ⊎ Test
