{-# OPTIONS --guardedness #-}
module Rational.Stream where

open import Data.Bool using (Bool; true; false)
open import Data.Nat
open import Data.Nat.Properties using (m*n≢0; +-comm)
open import Data.Nat.MoreProps using (Zero; zero; ¬Z&NZ)
open import Data.Fin as F using (Fin)
open import Data.Fin.MoreProps using (IsMax; fromℕ-ismax)
open import Data.Maybe hiding (map)
open import Data.Maybe.Relation.Unary.Any using (just)
-- open import Data.Vec as V using (Vec; []; _∷_)
-- open import Data.List.Snoc as L using (List)
open import Data.Vec.Snoc as V hiding (head)

open import Data.Product hiding (map)
open import Data.Unit
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.Isomorphism
open import Relation.Binary.PropositionalEquality
open import Function

{-
The idea is that rational fixpoints of containers (rational data types) are syntaxes with binding.
The point where we loop back is marked with a variable, the types use the sublime scoping machinery,
and other constructors may be binding sites.

In the case of rational streams, they are lists where every cons is a binder, and instead of empty list
we have a variable.
-}

private variable
  X : Set

-- The well-scoped de Bruijn version
data RStream (X : Set) (n : ℕ) : Set where
  loop : Fin n → RStream X n
  cons : X → RStream X (suc n) → RStream X n

data IsCons {X : Set} {n : ℕ} : RStream X n → Set where
  instance cons : ∀ {x xs} → IsCons (cons x xs)

-- Telescopic contexts for sublimely scoped streams.
data Ctx (X : Set) : ℕ → Set where
  [] : Ctx X 0
  _-,_ : ∀ {n} → Ctx X n → (xs : RStream X n) → {{_ : IsCons xs}} → Ctx X (suc n)

infixl 10 _-,_

inject₁ : ∀ {X n} → RStream X n → RStream X (suc n)
inject₁ (loop x) = loop (F.inject₁ x)
inject₁ (cons x xs) = cons x (inject₁ xs)

lookup : ∀ {X n} (Γ : Ctx X n) → Fin n → RStream X n
lookup (Γ -, xs) F.zero = inject₁ xs
lookup (Γ -, xs) (F.suc x) = inject₁ (lookup Γ x)

inject₁-preserves-IsCons : ∀ {X n} {xs : RStream X n} → IsCons xs → IsCons (inject₁ xs)
inject₁-preserves-IsCons cons = cons

lookup-IsCons : ∀ {X n} (Γ : Ctx X n) (x : Fin n) → IsCons (lookup Γ x)
lookup-IsCons (Γ -, cons x xs) F.zero = cons
lookup-IsCons (Γ -, cons x xs) (F.suc y) = inject₁-preserves-IsCons (lookup-IsCons Γ y)

lookup-elem : ∀ {X n} (Γ : Ctx X n) → Fin n → X
lookup-elem Γ x with lookup Γ x | lookup-IsCons Γ x
... | cons y ys | cons = y

----------------------
-- Ordinary streams --
----------------------

record Stream (X : Set) : Set where
  coinductive
  constructor _∷_
  field
    head : X
    tail : Stream X
open Stream

-- P becomes true in finitely many steps.
-- We want this to specifically point to nearest witness, hence the ¬ P head in the `there` case.
data Eventually {X : Set} (P : X → Set) (xs : Stream X) : Set where
  here  : P (head xs) → Eventually P xs
  there : ¬ (P (head xs)) → Eventually P (tail xs) → Eventually P xs

-- Predicate transformer for streams that extends a predicate P to be always true after every unfolding.
record Always {X : Set} (P : Stream X → Set) (xs : Stream X) : Set where
  coinductive
  field
    now     : P xs
    forever : Always P (tail xs)
open Always

-- If we know something is Eventually true, we can look ahead to the next witness.
next : {X : Set} {P : X → Set} {xs : Stream X} → Eventually P xs → X
next {xs = xs} (here px) = head xs
next {xs = xs} (there ¬px pxs) = next pxs

next-IsP : {X : Set} {P : X → Set} {xs : Stream X} (pxs : Eventually P xs) → P (next pxs)
next-IsP (here px) = px
next-IsP (there ¬px pxs) = next-IsP pxs

-- If we know that there are infinitely many P's, we can filter them out into a new stream.
filter' : {X : Set} {P : X → Set} → {xs : Stream X} → (pxs : Always (Eventually P) xs) → Stream (Σ[ x ∈ X ] (P x))
head (filter' pxs) = next (now pxs) , next-IsP (now pxs)
tail (filter' pxs) = filter' (forever pxs)

map : {X Y : Set} → (X → Y) → Stream X → Stream Y
head (map f xs) = f (head xs)
tail (map f xs) = map f (tail xs)

filter : {X : Set} {P : X → Set} → {xs : Stream X} → Always (Eventually P) xs → Stream X
filter = map proj₁ ∘ filter'

---------------
-- Unfolding --
---------------

-- We can unfold RStream to a Stream, so long as we leave in dummies where the variables were.
-- The termination checker gets cross otherwise :(
unfold' : ∀ {X n} → (Γ : Ctx X n) → RStream X n → Stream (Maybe X)
head (unfold' Γ (loop x)) = nothing
head (unfold' Γ (cons x xs)) = just x
tail (unfold' Γ (loop x)) = unfold' Γ (lookup Γ x)
tail (unfold' Γ (cons x xs)) = unfold' (Γ -, cons x xs) xs

-- As long as we can guarantee that we're always
-- only finitely many steps away from an X, we can remove all the 1's.
remove-dummies : ∀ {X} → {xs : Stream (Maybe X)} → Always (Eventually Is-just) xs → Stream X
remove-dummies pxs = map (λ px → to-witness (proj₂ px)) (filter' pxs)

unfold-lem : ∀ {X n} → (Γ : Ctx X n) (x : Fin n) → Is-just (head (unfold' Γ (lookup Γ x)))
unfold-lem Γ x with lookup Γ x | lookup-IsCons Γ x
... | .(cons _ _) | cons = just tt

-- And unfolding in particular does always eventually produce an X.
unfold-productive : ∀ {X n} → (Γ : Ctx X n) → (xs : RStream X n) → Always (Eventually Is-just) (unfold' Γ xs)
now (unfold-productive Γ (loop x)) = there (λ ()) (here (unfold-lem Γ x))
now (unfold-productive Γ (cons x xs)) = here (just tt)
forever (unfold-productive Γ (loop x)) = unfold-productive _ _
forever (unfold-productive Γ (cons x xs)) = unfold-productive _ _

-- Put the pieces together to get the real unfolding
unfold : ∀ {X n} → (Γ : Ctx X n) → RStream X n → Stream X
unfold Γ xs = remove-dummies (unfold-productive Γ xs)

-----------------------------------
-- Bisimilarity and Bisimulation --
-----------------------------------

-- Pointwise lifting of a binary relation to streams (from stdlib)
record Pointwise {X Y : Set} (_~_ : X → Y → Set) (xs : Stream X) (ys : Stream Y) : Set where
  coinductive
  field
    head : head xs ~ head ys
    tail : Pointwise _~_ (tail xs) (tail ys)

-- Bisimilarity is the pointwise lifting of equality
Bisimilar : ∀ {X} → Stream X → Stream X → Set
Bisimilar xs ys = Pointwise _≡_ xs ys

-- Bisimilarity of rational streams is bisimilarity of their unfoldings
BisimilarR' : ∀ {X i j} → Ctx X i → RStream X i → Ctx X j → RStream X j → Set
BisimilarR' Γ xs Δ ys = Bisimilar (unfold Γ xs) (unfold Δ ys)

BisimilarR : ∀ {X} → RStream X 0 → RStream X 0 → Set
BisimilarR xs ys = BisimilarR' [] xs [] ys



-----------
-- Loops --
-----------

-- An RStream is a loop if it loops back to the very start.
-- NB: This is not preserved by weakening.
IsLoop : {n : ℕ} → RStream X n → Set
IsLoop (loop x) = IsMax x
IsLoop (cons x l) = IsLoop l

-- As long as we know how far we've come, and that we've made at least some progress by the time we reach the end,
-- we can fold the list into a loop.
loopify' : ∀ {c} → (n : ℕ) → (xs : Vec X c) → (Zero c → NonZero n) → RStream X n
loopify' n [] p with p zero
loopify' (suc n) [] p | n' = loop (F.fromℕ n)
loopify' n (x ,- xs) p = cons x (loopify' (suc n) xs (const nonZero))

loopify : ∀ {c} (xs : Vec X c) → {{_ : NonZero c}} → RStream X 0
loopify xs {{nz}} = loopify' 0 xs (λ z → ⊥-elim (¬Z&NZ (z , nz)))

loopify-isloop : ∀ {c} n (xs : Vec X c) p → IsLoop (loopify' n xs p)
loopify-isloop n [] p with p zero
loopify-isloop (suc n) [] p | n' = fromℕ-ismax n
loopify-isloop n (x ,- xs) p = loopify-isloop (suc n) xs _



-------------------------
-- Algebraic Structure --
-------------------------

-- Two operations: unrolling, and loosening.
-- If two RStreams can be equalised by applications of these, then they
-- represent the same stream (ie, are bisimilar).


-- first, a definition on vectors.
-- And they all rolled over and one fell out...
rotate : ∀ {n} → Vec X n → Vec X n
rotate [] = []
rotate {n = suc n} (x ,- xs) rewrite +-comm 1 n = xs <<< (x ,- [])

extend : ∀ {p n} → Cev X p → RStream X n → RStream X n
extend = {!!}

-- We can view an RStream as a "lasso" - a finite prefix, and a nonempty looping section.
-- The explicit separation removes the need for a variable
record Lasso (X : Set) (|prefix| : ℕ) (|cycle| : ℕ) {{_ : NonZero |cycle|}} : Set where
  constructor _-∘_
  field
    prefix : Cev X |prefix|
    cycle  : Vec X |cycle|

  unroll : Lasso X (suc |prefix|) |cycle|
  prefix unroll = prefix -, V.head cycle
  cycle unroll = rotate cycle

  loosen : (k : ℕ) {{_ : NonZero k}} → Lasso X |prefix| (k * |cycle|) {{m*n≢0 _ _}}
  prefix (loosen k) = prefix
  cycle (loosen k) = repeat k cycle

  toRStream : RStream X 0
  toRStream = extend prefix (loopify cycle)

open Lasso



-- split rstream intp prefix and loop, for which the other view of RStreams would be *lovely*
toLasso : ∀ {X n p c} {{_ : NonZero c}} →  RStream X n → Lasso X p c
toLasso = {!!}



--------------------------------------
-- Proof that sqrt(2) is Irrational --
--------------------------------------

Digit = Fin 10

-- The unit interval of real numbers [0,1].
-- The stream contains the digits right of the decimal point.
I = Stream Digit


