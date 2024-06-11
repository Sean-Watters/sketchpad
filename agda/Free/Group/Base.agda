module Free.Group.Base where

open import Data.FreshList.InductiveInductive
open import Data.Unit
open import Data.Bool renaming (_≟_ to _≟B_)
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Function

open import Algebra.Definitions
open import Algebra.Structures

open import Relation.Const
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Relation.Nullary


data Signed (X : Set) : Set where
  mark : X → Bool → Signed X

_⁻¹ : ∀ {X} → Signed X → Signed X
_⁻¹ (mark x b) = mark x (not b)

liftDecEq : ∀ {X} → ((x y : X) → Dec (x ≡ y)) → ((x y : Signed X) → Dec (x ≡ y))
liftDecEq _=?_ (mark x b) (mark y b') with x =? y | b ≟B b'
... | yes refl | yes refl = yes refl
... | no ¬p | _ = no λ {refl → ¬p refl}
... | _ | no ¬p = no λ {refl → ¬p refl}

-- +x and -x are not fresh for each other, but are for everything else.
-- So it's enough to know that either the signs are the same, or the objects are different.
_-RG-_ : ∀ {X} → Signed X → Signed X → Set
mark x b -RG- mark y b' = (x ≢ y) ⊎ (b ≡ b')

FreeGroup : Set → Set
FreeGroup X = List# {A = Signed X} _-RG-_

-- Fix a carrier with decidable equality
module _ {X : Set} (_=?_ : (x y : X) → Dec (x ≡ y)) where
  open WithEq (_-RG-_ {X}) isEquivalence ((λ {x} → subst (x -RG-_)) , λ {y} → subst (_-RG- y))

  _∈?_ : (x : Signed X) (xs : FreeGroup X) → Dec (x ∈ xs)
  x ∈? xs = any? (liftDecEq _=?_ x) xs

  -- The characterisation of freshness that we care about;
  -- x if fresh for ys iff its inverse is not in ys.
  fresh-lemma : ∀ {x ys} → ¬ ((x ⁻¹) ∈ ys) → x # ys
  fresh-lemma {mark x b} {[]} p = []
  fresh-lemma {mark x b} {cons (mark y b') ys x#xs} p = {!p!} ∷ {!!} -- need to have a think about whether -RG- is formulated in the most useful way

  cancel : {x : Signed X} {xs : FreeGroup X}
         → (x ⁻¹) ∈ xs → FreeGroup X
  cancel-fresh : {x y : Signed X} {xs : FreeGroup X} → (p : (y ⁻¹) ∈ xs) → x # cancel p

  cancel {xs = xs} (here refl) = xs
  cancel {x} {cons y ys q} (there p) = cons y (cancel p) (cancel-fresh p)

  cancel-fresh {mark x b} {mark y b'} (here refl) = {!!} ∷ {!!}
  cancel-fresh (there p) = {!!}

  -- "insertion" here really means to cancel if theres an opposite signed element, and cons otherwise.
  -- And obviously cons if the maginitude is 0.
  insert : Signed X → FreeGroup X → FreeGroup X
  insert x ys with (x ⁻¹) ∈? ys
  ... | yes p = cancel p
  ... | no ¬p = cons x ys (fresh-lemma ¬p)

  _∙_ : FreeGroup X → FreeGroup X → FreeGroup X
  [] ∙ ys = ys
  cons x xs p ∙ ys = insert x (xs ∙ ys)
