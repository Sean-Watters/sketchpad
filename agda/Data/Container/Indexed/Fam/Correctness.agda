{-# OPTIONS --sized-types #-}

module Data.Container.Indexed.Fam.Correctness where


open import Level
open import Axiom.Extensionality.Propositional using (Extensionality) renaming (implicit-extensionality to exti)
open import Data.Container.Indexed.Fam
open import Data.Product
open import Data.Unit
open import Function
open import Relation.Binary.Isomorphism
open import Relation.Binary.PropositionalEquality hiding (J)


private
  variable
    I J : Set

module Identity (ext : Extensionality 0ℓ 0ℓ) where
  correct : (X : J → Set) → ⟦ ⟨id⟩ ⟧ X ≃ᵢ id X
  to (correct X) (tt , f) = f refl
  from (correct X) x = tt , λ { refl → x }
  from-to (correct X) (tt , f) = cong (tt ,_) (exti ext (ext (λ { refl → refl})))
  to-from (correct X) b = refl


module Constant (ext : Extensionality 0ℓ 0ℓ) where
  correct : (X Y : J → Set) → ⟦ ⟨const⟩ X ⟧ Y ≃ᵢ const X Y
  to (correct X Y) (x , _) = x
  from (correct X Y) x = x , λ {()}
  from-to (correct X Y) (x , _) = cong (x ,_) (exti ext (ext λ {()}))
  to-from (correct X Y) x = refl

module BinaryProduct (ext : Extensionality 0ℓ 0ℓ) where
  correct : (X : J → Set) → {!!}
  correct = {!!}

module IndexedProduct (ext : Extensionality 0ℓ 0ℓ) where
  correct : (X : J → Set) → {!!}
  correct = {!!}

module BinarySum (ext : Extensionality 0ℓ 0ℓ) where
  correct : (X : J → Set) → {!!}
  correct = {!!}

module IndexedSum (ext : Extensionality 0ℓ 0ℓ) where
  correct : (X : J → Set) → {!!}
  correct = {!!}

module LeastFixedPoint (ext : Extensionality 0ℓ 0ℓ) where
  correct : (X : J → Set) → {!!}
  correct = {!!}

module GreatestFixedPoint (ext : Extensionality 0ℓ 0ℓ) where
  correct : (X : J → Set) → {!!}
  correct = {!!}
