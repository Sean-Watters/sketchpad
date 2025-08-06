{-# OPTIONS --guardedness #-}
module Codata.CoFin where

open import Relation.Binary.PropositionalEquality

-------------------------------------------------------------------------------
-- Part 1: Co-Natural Numbers

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


-------------------------------------------------------------------------------
-- Part 2: Co-Finite Numbers (maybe?)

mutual
  record CoFin (n : CoNat) : Set where
    coinductive
    field
      inf : CoFin-step (CoNat.inf n)

  data CoFin-step : CoNat-step → Set where
    z : ∀ {n} → CoFin-step n
    s : ∀ {n} → CoFin n → CoFin-step (s n)

zero' : ∀ {n} → CoFin n
zero' .CoFin.inf = z

suc' : ∀ {n} → CoFin n → CoFin (suc n)
suc' n .CoFin.inf = s n

three' : CoFin three
three' = suc' (suc' (suc' zero'))

omega' : CoFin omega
omega' .CoFin.inf = s omega'

-------------------------------------------------------------------------------
-- Part 3: Casting `CoFin`s. It's a little cursed, but may come in handy

mutual
  record _≤_ (n m : CoNat) : Set where
    coinductive
    field
      inf : CoNat.inf n ≤-step CoNat.inf m

  data _≤-step_ : CoNat-step → CoNat-step → Set where
    z≤z : z ≤-step z
    s≤s : ∀ {n m} → n ≤ m → s n ≤-step s m

mutual
  cast : ∀ {n m} → n ≤ m → CoFin n → CoFin m
  cast n≤m x .CoFin.inf = cast-step (_≤_.inf n≤m) (CoFin.inf x)

  cast-step : ∀ {n m} → n ≤-step m → CoFin-step n → CoFin-step m
  cast-step _ z = z
  cast-step (s≤s n≤m) (s x) = s (cast n≤m x)
