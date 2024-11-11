{-# OPTIONS --safe --cubical-compatible #-}

-- Working with snoc lists.
module Data.List.Snoc where
open import Data.Product
open import Relation.Nullary

private variable
  X : Set

data List (X : Set) : Set where
  [] : List X
  _,-_ : X → List X → List X

data Empty {X : Set} : List X → Set where
  instance [] : Empty []

data NonEmpty {X : Set} : List X → Set where
  instance cons : ∀ {x xs} → NonEmpty (x ,- xs)

¬Empty&NonEmpty : ∀ {X} {xs : List X} → ¬ (Empty xs × NonEmpty xs)
¬Empty&NonEmpty ([] , ())

data Tsil (X : Set) : Set where
  [] : Tsil X
  _-,_ : Tsil X → X → Tsil X

head : (xs : List X) → {{_ : NonEmpty xs}} → X
head (x ,- xs) = x

_><<_ : Tsil X → List X → List X
[] ><< ys = ys
(sx -, x) ><< ys = sx ><< (x ,- ys)

_><>_ : Tsil X → List X → Tsil X
sx ><> [] = sx
sx ><> (x ,- xs) = (sx -, x) ><> xs

record Zipper (X : Set) : Set where
  constructor _,_
  field
    front : Tsil X
    back : List X
open Zipper
