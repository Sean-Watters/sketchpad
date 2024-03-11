{-# OPTIONS --safe --cubical-compatible #-}

open import Level
open import Axiom.Extensionality.Propositional

open import Data.Product
open import Relation.Binary.Isomorphism
open import Relation.Binary.PropositionalEquality

module Exercises.PowFamFlip
  {ℓ : Level} (I : Set ℓ) --
  (ext : ∀ {a b} → Extensionality a b)
  where

----------------------------------------------
--  CLAIM : (I → Set) ≊ Σ(X : Set).(X → I)  --
----------------------------------------------

-- Intuitively, an indexed family is a collection ("family")
-- of sets; a set for each element of the indexing set, I.
-- We can imagine "gluing" all of the sets in the family together
-- to form one set, X. We can split X apart into the family again
-- so long as we have a function (X → I) which tells us which index
-- each element belonged to.

-----------
-- Proof --
-----------

-- To glue together all the members of the family P, we take the type of
-- pairs of an index (i : I) together with its set (P i). The function which
-- tells us which index each element came from is just the projection of that i.
fam→pow : (I → Set ℓ) → (Σ[ X ∈ Set ℓ ] (X → I))
fam→pow P = (Σ[ i ∈ I ] P i) , proj₁

-- To recover the member of the family at some index i, we take the subtype
-- of all those X's that map back to i. That is, the type of pairs of an (x : X)
-- and a proof that (f x ≡ i), where f is our indexing function (f : X → I).
-- Such a dependent pair is called a *fiber*; specifically, the fiber of f at i.
-- And we have such a fiber for each (i : I); a family of fibers like this is called
-- a *fibration* (todo: check that this is actually what a fibration is.....)
pow→fam : (Σ[ X ∈ Set ℓ ] (X → I)) → (I → Set ℓ)
pow→fam (X , f) = λ i → Σ[ x ∈ X ] (f x ≡ i)

-- Proving both directions of the isomorphism is made trivial by dependent pattern
-- matching. Without that sledgehammer, you can imagine transporting along the
-- equalities. See eg, Introduction to HoTT, Egbert Rijke

pow→fam→pow : (P : Σ[ X ∈ Set ℓ ] (X → I)) → proj₁ (fam→pow (pow→fam P)) ≃ proj₁ P
to (pow→fam→pow (X , f)) (.(f x) , x , refl) = x
from (pow→fam→pow (X , f)) x = (f x) , (x , refl)
from-to (pow→fam→pow (X , f)) (.(f x) , x , refl) = refl
to-from (pow→fam→pow (X , f)) b = refl

fam→pow→fam : (P : I → Set ℓ) → (i : I) → (pow→fam (fam→pow P)) i ≃ P i
to (fam→pow→fam P i) ((.i , Pi) , refl) = Pi
from (fam→pow→fam P i) x = (i , x) , refl
from-to (fam→pow→fam P i) ((.i , Pi) , refl) = refl
to-from (fam→pow→fam P i) b = refl
