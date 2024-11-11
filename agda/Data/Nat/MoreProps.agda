module Data.Nat.MoreProps where

open import Algebra.Structures.Propositional
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

data Zero : ℕ → Set where
  instance zero : Zero zero

¬Z&NZ : {n : ℕ} → ¬ (Zero n × NonZero n)
¬Z&NZ (zero , ())

≤-stepL : ∀ {x y} → suc x ≤ y → x ≤ y
≤-stepL (s≤s z≤n) = z≤n
≤-stepL (s≤s (s≤s x)) = s≤s (≤-stepL (s≤s x))

<-isPropStrictTotalOrder : IsPropStrictTotalOrder _≡_ _<_
IsPropStrictTotalOrder.isSTO <-isPropStrictTotalOrder = <-isStrictTotalOrder
IsPropStrictTotalOrder.≈-prop <-isPropStrictTotalOrder = ≡-irrelevant
IsPropStrictTotalOrder.<-prop <-isPropStrictTotalOrder = ≤-irrelevant

>-isPropStrictTotalOrder : IsPropStrictTotalOrder _≡_ _>_
>-isPropStrictTotalOrder = IsPropStrictTotalOrder.flip-PSTO <-isPropStrictTotalOrder
