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

mutual
  _+_ : CoNat → CoNat → CoNat
  (x + y) .CoNat.inf = CoNat.inf x +-step CoNat.inf y

  _+-step_ : CoNat-step → CoNat-step → CoNat-step
  z +-step y = y
  s x +-step y = s (x + ⟨ y ⟩)

mutual
  min : CoNat → CoNat → CoNat
  min x y .CoNat.inf = min-step (CoNat.inf x) (CoNat.inf y)

  min-step : CoNat-step → CoNat-step → CoNat-step
  min-step z y = z
  min-step (s x) z = z
  min-step (s x) (s y) = {!min x y!} -- no hope here. and it makes sense; we can't compute `min omega omega`

-------------------------------------------------------------------------------
-- Part 2: Co-Finite Numbers (maybe?)

mutual
  record CoFin (n : CoNat) : Set where
    constructor ⟪_⟫
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
-- Part 3: Some operations on CoFins

mutual
  record _≤_ (n m : CoNat) : Set where
    coinductive
    field
      inf : CoNat.inf n ≤-step CoNat.inf m

  data _≤-step_ : CoNat-step → CoNat-step → Set where
    z≤n : ∀ {n} → z ≤-step n
    s≤s : ∀ {n m} → n ≤ m → s n ≤-step s m

mutual
  cast : ∀ {n m} → n ≤ m → CoFin n → CoFin m
  cast n≤m x .CoFin.inf = cast-step (_≤_.inf n≤m) (CoFin.inf x)

  cast-step : ∀ {n m} → n ≤-step m → CoFin-step n → CoFin-step m
  cast-step _ z = z
  cast-step (s≤s n≤m) (s x) = s (cast n≤m x)

mutual
  ≤-refl : ∀ n → n ≤ n
  ≤-refl n ._≤_.inf = ≤-refl-step (CoNat.inf n)

  ≤-refl-step : ∀ n → n ≤-step n
  ≤-refl-step z = z≤n
  ≤-refl-step (s n) = s≤s (≤-refl n)

mutual
  ≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
  ≤-trans p q ._≤_.inf = ≤-trans-step (p ._≤_.inf) (q ._≤_.inf)

  ≤-trans-step : ∀ {x y z} → x ≤-step y → y ≤-step z → x ≤-step z
  ≤-trans-step z≤n q = z≤n
  ≤-trans-step (s≤s p) (s≤s q) = s≤s (≤-trans p q)

mutual
  m≤n+m : ∀ n m → m ≤ (n + m)
  m≤n+m n m ._≤_.inf = m≤n+m-step (CoNat.inf n) (CoNat.inf m)

  m≤n+m-step : ∀ n m → m ≤-step (n +-step m)
  m≤n+m-step z m = ≤-refl-step m
  m≤n+m-step (s x) z = z≤n
  m≤n+m-step (s x) (s y) = s≤s (≤-trans (m≤n+m x y) {!!})
  -- oh, right. can't do compositional proof for codata without NAD's DSL approach...

mutual
  _+'_ : ∀ {n m} → CoFin n → CoFin m → CoFin (n + m)
  (x +' y) .CoFin.inf = (CoFin.inf x) +-step' (CoFin.inf y)

  _+-step'_ : ∀ {n m} → CoFin-step n → CoFin-step m → CoFin-step (n +-step m)
  z +-step' y = cast-step {!!} y
  (s x) +-step' y = s (x +' ⟪ y ⟫)
