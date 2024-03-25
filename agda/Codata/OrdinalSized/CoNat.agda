{-# OPTIONS --safe --guardedness #-}
module Codata.OrdinalSized.CoNat where

open import CoData.OrdinalSized.Core
open import Data.Product

data Coℕ (i : Size) : Set where
  zero : Coℕ i
  suc : Thunk Coℕ i → Coℕ i

0cn : ∀ {i} → Coℕ i
0cn = zero

1cn : ∀ {i} → Coℕ i
1cn = suc (delay (λ _ → zero))

2cn : ∀ {i} → Coℕ i
2cn = suc (delay (λ j<i → suc (delay (λ j<i₁ → zero))))

infinity : ∀ {i} → Coℕ i
infinity = suc (delay (λ j<i → {!infinity!}))

sucf : ∀ {i} → Coℕ i → Coℕ (sucs i)
sucf {* , pκ} zero = {!!}
sucf {* , pκ} (suc x) = {!!}
sucf {(κ ^+ κ₁) , pκ} x = {!!}
