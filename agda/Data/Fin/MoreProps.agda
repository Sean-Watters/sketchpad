{-# OPTIONS --with-K #-}
module Data.Fin.MoreProps where

open import Data.Fin
open import Data.Fin.Properties
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.WithK
open import Algebra.Structures.Propositional

<-isPropStrictTotalOrder : ∀ n → IsPropStrictTotalOrder (_≡_ {A = Fin n}) _<_
IsPropStrictTotalOrder.isSTO (<-isPropStrictTotalOrder n) = <-isStrictTotalOrder
IsPropStrictTotalOrder.≈-prop (<-isPropStrictTotalOrder n) = ≡-irrelevant
IsPropStrictTotalOrder.<-prop (<-isPropStrictTotalOrder n) = ≤-irrelevant
