{-# OPTIONS --safe --guardedness #-}
module Rational.Stream where

open import Data.Nat
open import Data.Fin as F using (Fin)
open import Data.Maybe
open import Data.Unit
open import Relation.Binary.Isomorphism

{-
The idea is that rational fixpoints of containers (rational data types) are syntaxes with binding.
The point where we loop back is marked with a variable, the types use the sublime scoping machinery,
and other constructors may be binding sites.

In the case of rational streams, they are lists where every cons is a binder, and instead of empty list
we have a variable.
-}

-- The well-scoped de Bruijn version
data RStream' (X : Set) (n : ℕ) : Set where
  loop : Fin n → RStream' X n
  cons : X → RStream' X (suc n) → RStream' X n

data IsCons {X : Set} {n : ℕ} : RStream' X n → Set where
  instance cons : ∀ {x xs} → IsCons (cons x xs)

-- The richer contexts for the sublime scopes
data Ctx (X : Set) : ℕ → Set where
  [] : Ctx X 0
  _-,_ : ∀ {n} → Ctx X n → (xs : RStream' X n) → {{_ : IsCons xs}} → Ctx X (suc n)

-- Sublimely scoped RStreams
mutual
  data RStream {X : Set} {n : ℕ} (Γ : Ctx X n) : Set where
    loop : Fin n → RStream Γ
    cons : (x : X) → {xs' : RStream' X (suc n)} → (xs : RStream (Γ -, (cons x xs'))) → xs' ≈ xs → RStream Γ

  data _≈_ {X : Set} {n : ℕ} {Γ : Ctx X n} : RStream' X n → RStream Γ → Set where
    loop : ∀ {x} → loop x ≈ loop x
    _∷_ : ∀ {x xs' xs} → (p : xs' ≈ xs) → (cons x xs') ≈ (cons x xs p)

-- We can annotate with fancy contexts
WS→SS : ∀ {X n} → (Γ : Ctx X n) → RStream' X n → RStream Γ
WS→SS Γ (loop x) = loop x
WS→SS Γ (cons x xs) = cons x (WS→SS {!!} xs) {!!}

-- We can forget the fancy contexts
SS→WS : ∀ {X n} {Γ : Ctx X n} → RStream Γ → RStream' X n
SS→WS (loop x) = loop x
SS→WS (cons x {xs'} xs _) = cons x xs'

-- And we get an isomorphism between the WS and SS versions
iso : ∀ {X n} → (Γ : Ctx X n) → RStream' X n ≃ RStream Γ
iso = {!!}

lookup : ∀ {X n} (Γ : Ctx X n) → Fin n → RStream' X n
lookup Γ x = {!!}

lookup-iscons : ∀ {X n} (Γ : Ctx X n) → (x : Fin n) → IsCons (lookup Γ x)
lookup-iscons = {!!}

-- Ordinary streams
record Stream (X : Set) : Set where
  coinductive
  constructor _∷_
  field
    head : X
    tail : Stream X

-- We can unfold RStream to a Stream, so long as we leave in dummies where the variables were.
-- The termination checker gets cross otherwise :(
unfold : ∀ {X n} {Γ : Ctx X n} → RStream Γ → Stream (Maybe X)
Stream.head (unfold (loop x)) = nothing
Stream.head (unfold (cons x xs p)) = just x
Stream.tail (unfold {Γ = Γ} (loop x)) = unfold {Γ = Γ} (WS→SS _ (lookup Γ x))
Stream.tail (unfold (cons x xs p)) = unfold xs


-- Liveness : given a (xs : Stream X) and a (P : X → Set), there's some upper bound (n : ℕ) such that we
-- can take always take fewer than n steps in xs to reach the next P x.
Live : {X : Set} → (P : X → Set) → Stream X → Set
Live P xs = {!!}


-- As long as we can guarantee that we're always
-- only finitely many steps away from an X, we can remove all the 1's.
remove-dummies : ∀ {X} → (xs : Stream (Maybe X)) → Live {!!} xs → Stream X
remove-dummies = {!!}
