
{-# OPTIONS --safe --cubical-compatible #-}

-- Working with snoc lists.
module Data.Vec.Snoc where
open import Data.Product
open import Data.Nat
open import Data.Nat.Properties
open import Data.List.Snoc using (List; Tsil; []; _,-_; _-,_)
open import Data.Vec using (Vec; []) renaming (_∷_ to _,-_; _++_ to _<<<_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

private variable
  X : Set

data Cev (X : Set) : ℕ → Set where
  [] : Cev X 0
  _-,_ : ∀ {n} → Cev X n → X → Cev X (suc n)

head : ∀ {n} → (xs : Cev X n) {{_ : NonZero n}} → X
head (sx -, x) = x

_><<_ : ∀ {n m} → Cev X n → Vec X m → Vec X (n + m)
[] ><< ys = ys
_><<_ {n = suc n} {m} (sx -, x) ys rewrite sym (+-suc n m) = sx ><< (x ,- ys)

_><>_ : ∀ {n m} → Cev X n → Vec X m → Cev X (n + m)
_><>_ {n = n} sx [] rewrite +-identityʳ n = sx
_><>_ {n = n} {suc m} sx (x ,- xs) rewrite (+-suc n m) = (sx -, x) ><> xs

-- _<><_ : ∀ {n m} → Vec X n → Cev X m → Vec X (n + m)
-- _<><_ = {!!}

-- _>>>_ : ∀ {n m} → Cev X n → Cev X m → Cev X (n + m)
-- _>>>_ = {!!}

-- This is the inefficient way, but meh
rev : ∀ {n} → Cev X n → Vec X n
rev [] = []
rev {n = suc n} (sx -, x) rewrite +-comm 1 n = (rev sx) <<< (x ,- [])

data Any {X : Set} (P : X → Set) : ∀ {n} → Cev X n → Set where
  here : ∀ {n x} {sx : Cev X n} → P x → Any P (sx -, x)
  there : ∀ {n x} {sx : Cev X n} → Any P sx → Any P (sx -, x)

_∈_ : {X : Set} → X → {n : ℕ} → Cev X n → Set
x ∈ sx = Any (x ≡_) sx

-------------
-- Zippers --
-------------

-- record Zipper (X : Set) : Set where
--   constructor _>[_]<_
--   field
--     front : Tsil X
--     focus : X
--     back : List X
-- open Zipper
