{-# OPTIONS --safe #-}

module Data.Container.Indexed.Fam.SmallIR where

open import Data.Container.Indexed.Fam

-- Dybjer-Setzer IR codes. *Small* IR because I and O are sets, not larger.
data IR (I O : Set) : Set₁ where
  ι : O → IR I O
  σ : (S : Set) → (S → IR I O) → IR I O
  δ : (P : Set) → ((P → I) → IR I O) → IR I O

toCont : ∀ {I O} → IR I O → Container I O
toCont = {!!}
