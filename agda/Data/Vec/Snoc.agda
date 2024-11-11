
{-# OPTIONS --safe --cubical-compatible #-}

-- Working with snoc lists.
module Data.Vec.Snoc where
open import Data.Product
open import Data.Nat
open import Data.Nat.Properties
open import Data.List.Snoc using (List; Tsil; []; _,-_; _-,_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

private variable
  X : Set

data Vec (X : Set) : ℕ → Set where
  [] : Vec X 0
  _,-_ : ∀ {n} → X → Vec X n → Vec X (suc n)

data Cev (X : Set) : ℕ → Set where
  [] : Cev X 0
  _-,_ : ∀ {n} → Cev X n → X → Cev X (suc n)

head : ∀ {n} → (xs : Vec X n) {{_ : NonZero n}} → X
head (x ,- xs) = x

_><<_ : ∀ {n m} → Cev X n → Vec X m → Vec X (n + m)
[] ><< ys = ys
_><<_ {n = suc n} {m} (sx -, x) ys rewrite sym (+-suc n m) = sx ><< (x ,- ys)

_><>_ : ∀ {n m} → Cev X n → Vec X m → Cev X (n + m)
_><>_ {n = n} sx [] rewrite +-identityʳ n = sx
_><>_ {n = n} {suc m} sx (x ,- xs) rewrite (+-suc n m) = (sx -, x) ><> xs

_<<<_ : ∀ {n m} → Vec X n → Vec X m → Vec X (n + m)
_<<<_ [] ys = ys
_<<<_ (x ,- xs) ys = x ,- (xs <<< ys)

repeat : ∀ {n} → (k : ℕ) → Vec X n → Vec X (k * n)
repeat zero xs = []
repeat (suc k) xs = xs <<< repeat k xs

-- record Zipper (X : Set) : Set where
--   constructor _,_
--   field
--     front : Tsil X
--     back : List X
-- open Zipper
