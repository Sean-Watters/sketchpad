{-# OPTIONS --guardedness #-}
module Codata.CoFin where

open import Relation.Binary.PropositionalEquality

mutual
  record CoNat : Set where
    coinductive
    constructor ⟨_⟩
    field
      inf : CoNat-step

  data CoNat-step : Set where
    z : CoNat-step
    s : CoNat → CoNat-step

zero : CoNat
zero = ⟨ z ⟩

suc : CoNat → CoNat
suc n = ⟨ s n ⟩

three : CoNat
three = suc (suc (suc zero))

omega : CoNat
omega .CoNat.inf = s omega




mutual
  record CoFin (n : CoNat) : Set where
    coinductive
    field
      inf : CoFin-step n

  data CoFin-step : CoNat → Set where
    z : ∀ {n} → CoFin-step n
    s : ∀ {n} → CoFin n → CoFin-step ⟨ s n ⟩

zero' : ∀ {n} → CoFin n
zero' .CoFin.inf = z

suc' : ∀ {n} → CoFin n → CoFin (suc n)
suc' n .CoFin.inf = s n

three' : CoFin three
three' = suc' (suc' (suc' zero'))


omega' : CoFin omega
omega' .CoFin.inf = {!!}
