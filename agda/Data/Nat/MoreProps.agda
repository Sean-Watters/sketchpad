module Data.Nat.MoreProps where

open import Data.Nat
open import Data.Nat.Properties

≤-stepL : ∀ {x y} → suc x ≤ y → x ≤ y
≤-stepL (s≤s z≤n) = z≤n
≤-stepL (s≤s (s≤s x)) = s≤s (≤-stepL (s≤s x))
