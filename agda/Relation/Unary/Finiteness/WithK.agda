{-# OPTIONS --with-K #-}
module Relation.Unary.Finiteness.WithK where

open import Algebra.Structures.Propositional
open import Data.Unit
open import Data.Empty
open import Data.List
open import Data.List.Relation.Unary.Any hiding (lookup)
open import Data.Product
open import Data.List.Membership.Propositional
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.MoreProps
open import Data.Fin using (Fin; fromℕ<) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.MoreProps renaming (<-isPropStrictTotalOrder to FinSTO)
open import Relation.Binary.Isomorphism
open import Relation.Binary.PropositionalEquality

open import Data.FreshList.InductiveInductive
open import Free.IdempotentCommutativeMonoid using (SortedList; insert) renaming (_∈_ to member)

-- Enumerated types are those with a finite enumeration

is-enumeration : (X : Set) (L : List X) → Set
is-enumeration X L = (x : X) → x ∈ L

-- An enumerated type is one where there exists some list
-- L which contains all of the elements of the type.
Enumerated : Set → Set
Enumerated X = ∃[ L ] (is-enumeration X L)

-- A stronger notion of enumeration is to use a sorted list; this ensures canonicity
-- relative to a particular ordering on the type.
is-strong-enumeration : {X : Set} {_<_ : X → X → Set} (X-STO : IsPropStrictTotalOrder _≡_ _<_) (L : SortedList X-STO) → Set
is-strong-enumeration {X} X-STO L = (x : X) → member X-STO x L

-- nb: this one is proof relevant!
StronglyEnumerated : {X : Set} {_<_ : X → X → Set} (X-STO : IsPropStrictTotalOrder _≡_ _<_) → Set
StronglyEnumerated {X} X-STO = Σ[ L ∈ SortedList X-STO ] is-strong-enumeration X-STO L

---------------
-- Instances --
---------------

Fin-enum : ∀ n → StronglyEnumerated (FinSTO n)
Fin-enum n = {!!} , {!!} where
  enumerate : (m n : ℕ) → m ≤ n → SortedList (FinSTO n)
  enumerate m n p = {!!}

  is-enum : {! is-strong-enumeration (FinSTO n) (enumerate n) !}
  is-enum = {!!}

{-
-- Another notion of finiteness is when a type is isomorphic to Fin
Finite : Set → Set
Finite X = ∃[ n ] X ≃ Fin n


-- These two notions are isomorphic -- edit: no they're not! the list having duplicates is a problem
Fin→Enum : ∀ X → Finite X → Enumerated X
Fin→Enum X (n , iso) = (enumerate n ≤-refl) , is-enum n ≤-refl where
  enumerate : (m : ℕ) → m ≤ n → List X
  enumerate zero _ = []
  enumerate (suc m) p = from iso (fromℕ< p) ∷ enumerate m (≤-stepL p)

  is-enum : (m : ℕ) → (p : m ≤ n) → is-enumeration X (enumerate m p)
  is-enum zero z≤n x = {!!} -- something is wrong somewhere
  is-enum (suc m) p x = {!!}

-- Add to stdlib under Any.Properties?
lookup-index : {X : Set} (a : X) (xs : List X) → (p : a ∈ xs) → a ≡ lookup xs (index p)
lookup-index a (x ∷ xs) (here  p) = p
lookup-index a (x ∷ xs) (there p) = lookup-index a xs p

index-enum : {X : Set} (xs : List X) (enum : is-enumeration X xs) (i : Fin (length xs)) → i ≡ index (enum (lookup xs i))
index-enum (x ∷ xs) enum fzero = {!enum x!} -- problem: we can see that x is clearly at the head, but there's no guarantee that it isn't duplicated elsewhere.
                                            -- moreover, if x does appear elsewhere in xs, enum may always choose that later occurrence, which we don't want.
                                            -- another use case of sorted lists?
index-enum (x ∷ xs) enum (fsuc i) = {!!}

Enum→Fin : ∀ X → Enumerated X → Finite X
Enum→Fin X (L , enum) = length L , iso where
  iso : X ≃ Fin (length L)
  to iso x = index (enum x)
  from iso x = lookup L x
  from-to iso a = lookup-index a L (enum a)
  to-from iso i = index-enum L enum i

Finite≃Enumerated : ∀ X → Finite X ≃ Enumerated X
Finite≃Enumerated X = {!!}

-- todo: instead of proving the ordering directly like so, it's probably neater to
-- go via the sensible ordering on fins
_<∈_ : {X : Set} {x y : X} {xs : List X} → (x ∈ xs → y ∈ xs → Set)
here  p <∈ here  q = ⊥ -- x=y, so x≮y
here  p <∈ there q = ⊤ -- x<y
there p <∈ here  q = ⊥ -- x>y, so x≮y
there p <∈ there q = p <∈ q

enum⇒ord : ∀ {X L} → is-enumeration X L → (X → X → Set)
enum⇒ord {X} {L} enum x y = (enum x) <∈ (enum y) 

-}
