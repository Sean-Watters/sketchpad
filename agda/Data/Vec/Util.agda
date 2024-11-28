{-# OPTIONS --safe --cubical-compatible #-}
module Data.Vec.Util where

open import Data.Vec
open import Data.Nat

private variable
  X : Set

repeat : ∀ {n} → (k : ℕ) → Vec X n → Vec X (k * n)
repeat zero xs = []
repeat (suc k) xs = xs ++ repeat k xs

head-nz : ∀ {n} {{_ : NonZero n}} → Vec X n → X
head-nz (x ∷ xs) = x
