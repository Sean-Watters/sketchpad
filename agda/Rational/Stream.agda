{-# OPTIONS --guardedness #-}
module Rational.Stream where

open import Axiom.Extensionality.Propositional
open import Data.Bool using (Bool; true; false)
open import Data.Nat
open import Data.Nat.Properties using (m*n≢0; +-comm)
open import Data.Nat.MoreProps using (Zero; zero; ¬Z&NZ)
open import Data.Fin as F using (Fin)
open import Data.Fin.MoreProps using (IsMax; fromℕ-ismax)
open import Data.Maybe hiding (map)
open import Data.Maybe.Relation.Unary.Any using (just)
-- open import Data.Vec as V using (Vec; []; _∷_)
open import Data.List as L using (List; []; _∷_)
open import Data.Vec.Snoc as V> using (Cev; []; _-,_)
open import Data.Vec as V< using (Vec; []) renaming (_∷_ to _,-_; _++_ to _<<<_)
open import Data.Vec.Util as V<
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


--------------------------------
-- Rescoping and Substitution --
--------------------------------

-- Scope extension
ext : ∀ {i j} → (Fin i → Fin j)
    → Fin (suc i) → Fin (suc j)
ext ρ F.zero = F.zero
ext ρ (F.suc x) = F.suc (ρ x)

rescope : ∀ {X n m} → (Fin n → Fin m) → RStream X n → RStream X m
rescope ρ (loop x) = loop (ρ x)
rescope ρ (cons x xs) = cons x (rescope (ext ρ) xs )

inject₁ : ∀ {X n} → RStream X n → RStream X (suc n)
inject₁ = rescope F.inject₁

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
-- We want this to specifically point to nearest witness, hence the ¬(P head) in the `there` case.
data Eventually {X : Set} (P : X → Set) (xs : Stream X) : Set where
  here  : (px : P (head xs)) → Eventually P xs
  there : (¬px : ¬ (P (head xs))) → (pxs : Eventually P (tail xs)) → Eventually P xs

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

-- Evidence that a particular X is the next witness to an Eventually.
-- This is, by no coincidece, the graph of `next`. It's useful for avoiding green slime.
data Next {X : Set} {P : X → Set} {xs : Stream X} : Eventually P xs → {x : X} → P x → Set where
  here : (px : P (head xs)) → Next (here px) px
  there : {x : X} {nx : P x} (¬px : ¬ (P (head xs))) (pxs : Eventually P (tail xs)) → Next pxs nx → Next (there ¬px pxs) nx

-- `next` really does give the Next. This is basically true by definition.
next-Next : {X : Set} {P : X → Set} {xs : Stream X} → (pxs : Eventually P xs) → Next pxs (next-IsP pxs)
next-Next (here px) = here px
next-Next (there ¬px pxs) = there ¬px pxs (next-Next pxs)

-- Next is computable, obviously via the above `next` function
next-computable : {X : Set} {P : X → Set} {xs : Stream X} → (pxs : Eventually P xs) → Σ[ x ∈ X ] Σ[ px ∈ P x ] Next pxs px
next-computable pxs = next pxs , next-IsP pxs , next-Next pxs

-- Part 1
-- If we have a Next, then it points to the *unique* next element.
next-unique : {X : Set} {P : X → Set} {xs : Stream X} {pxs : Eventually P xs} {x x' : X} {px : P x} {px' : P x'}
            → Next pxs px → Next pxs px' → x ≡ x'
next-unique (here p) (here q) = refl
next-unique (there ¬px pxs n1) (there .¬px .pxs n2) = next-unique n1 n2

-- Part 2!
-- The proof P x is also unique.
next-unique-proof : {X : Set} {P : X → Set} {xs : Stream X} {pxs : Eventually P xs} {x : X} {px px' : P x}
                  → Next pxs px → Next pxs px' → px ≡ px'
next-unique-proof (here p) (here q) = refl
next-unique-proof (there ¬px pxs n1) (there .¬px .pxs n2) = next-unique-proof n1 n2

-- Part 3!
-- Next itself is propositional.
Next-propositional : {X : Set} {P : X → Set} {xs : Stream X} {pxs : Eventually P xs} {x : X} {px : P x}
                 → (n1 n2 : Next pxs px) → n1 ≡ n2
Next-propositional (here p) (here q) = refl
Next-propositional (there ¬px pxs n1) (there .¬px .pxs n2) = cong (there ¬px pxs) (Next-propositional n1 n2)

-- What does it mean for two streams to have the same next element?
record EqNexts {X : Set} {P : X → Set} {xs ys : Stream X} (pxs : Eventually P xs) (pys : Eventually P ys) : Set where
  constructor [_,_,_]
  field
    {x y} : X
    {px} : P x
    {py} : P y
    nx : Next pxs px         -- x is the next P in xs...
    ny : Next pys py         -- y is the next P in ys...
    eq : x ≡ y               -- and x=y...
    eq' : subst P eq px ≡ py -- and px=py.

  eq-next-elem : next pxs ≡ next pys
  eq-next-elem = trans (sym $ next-unique nx (next-Next pxs)) (trans eq (next-unique ny (next-Next pys)))

  eq-next-proof : subst P eq-next-elem (next-IsP pxs) ≡ next-IsP pys
  eq-next-proof = {!!}

  eq-next : _≡_ {A = Σ[ x ∈ X ] P x} (next pxs , next-IsP pxs) (next pys , next-IsP pys)
  eq-next = dcong₂ _,_ eq-next-elem eq-next-proof

-- If we know that there are infinitely many P's, we can filter them out into a new stream.
filter' : {X : Set} {P : X → Set} → {xs : Stream X} → (pxs : Always (Eventually P) xs) → Stream (Σ[ x ∈ X ] (P x))
head (filter' pxs) = next (now pxs) , next-IsP (now pxs)
tail (filter' pxs) = filter' (forever pxs)

map : {X Y : Set} → (X → Y) → Stream X → Stream Y
head (map f xs) = f (head xs)
tail (map f xs) = map f (tail xs)

-- filter : {X : Set} {P : X → Set} → {xs : Stream X} → Always (Eventually P) xs → Stream X
-- filter = map proj₁ ∘ filter'


-----------------------------------
-- Bisimilarity and Bisimulation --
-----------------------------------

-- lifting of a binary relation to streams (from stdlib)
record Pointwise {X Y : Set} (_~_ : X → Y → Set) (xs : Stream X) (ys : Stream Y) : Set where
  coinductive
  field
    head : head xs ~ head ys
    tail : Pointwise _~_ (tail xs) (tail ys)
open Pointwise

-- Bisimilarity is the pointwise lifting of equality
_~_ : ∀ {X} → Stream X → Stream X → Set
xs ~ ys = Pointwise _≡_ xs ys

-- lifting of a homogenous binary relation to Always
record PointwiseAlways {X : Set} {P : Stream X → Set} (_~_ : ∀ {xs ys} → P xs → P ys → Set) {xs ys : Stream X} (pxs : Always P xs) (pys : Always P ys) : Set where
  coinductive
  field
    now : now pxs ~ now pys
    forever : PointwiseAlways _~_ (forever pxs) (forever pys)
open PointwiseAlways

-- At every step, the two streams must b equal on their next P's.
-- Ezra says this is weak bisimilarity.
WBisimilar : ∀ {X} {xs ys : Stream X} (P : X → Set) → Always (Eventually P) xs → Always (Eventually P) ys → Set
WBisimilar P = PointwiseAlways EqNexts

-- -- Bisimilarity of rational streams is bisimilarity of their unfoldings
-- BisimilarR' : ∀ {X i j} → Ctx X i → RStream X i → Ctx X j → RStream X j → Set
-- BisimilarR' Γ xs Δ ys = Bisimilar (unfold Γ xs) (unfold Δ ys)

-- BisimilarR : ∀ {X} → RStream X 0 → RStream X 0 → Set
-- BisimilarR xs ys = BisimilarR' [] xs [] ys

-- Equality implies bisimilarity. But not vice versa (in MLTT)!
≡→~ : ∀ {X} → {xs ys : Stream X} → xs ≡ ys → xs ~ ys
head (≡→~ refl) = refl
tail (≡→~ refl) = ≡→~ refl


-- The lookup function for streams; aka how to turn streams into functions ℕ→X
lookup-stream : ∀ {X} → Stream X → ℕ → X
lookup-stream xs zero = head xs
lookup-stream xs (suc n) = lookup-stream (tail xs) n

-- Tabulate a countable function
tabulate : ∀ {X} → (ℕ → X) → Stream X
head (tabulate f) = f 0
tail (tabulate f) = tabulate (f ∘ suc)

-- This is only provable up to bisimilarity
tabulate-lookup : ∀ {X} → (xs : Stream X) → (tabulate (lookup-stream xs)) ~ xs
head (tabulate-lookup xs) = refl
tail (tabulate-lookup xs) = tabulate-lookup (tail xs)

-- We need funext to ro
module WithFunext (funext : ∀ {a b} → Extensionality a b) where

  lookup-tabulate : ∀ {X} → (f : ℕ → X) → f ≡ lookup-stream (tabulate f)
  lookup-tabulate {X} g = funext (go g) where
    go : (f : ℕ → X) (x : ℕ) → f x ≡ lookup-stream (tabulate f) x
    go f zero = refl
    go f (suc x) = go (f ∘ suc) x

  bisim→lookup-eq : ∀ {X} {xs ys : Stream X} → xs ~ ys → lookup-stream xs ≡ lookup-stream ys
  bisim→lookup-eq {X} Z = funext (go Z) where
    go : ∀ {xs ys : Stream X} (Z : xs ~ ys) (x : ℕ) → lookup-stream xs x ≡ lookup-stream ys x
    go Z zero = head Z
    go Z (suc x) = go (tail Z) x

  -- StreamIso : ∀ {X} → Stream X ≃ (ℕ → X)
  -- to StreamIso = lookup-stream
  -- from StreamIso = tabulate
  -- from-to StreamIso = {!tabulate-lookup!}
  -- to-from StreamIso = lookup-tabulate

-- -- I think if this were a theorem, then it would imply bisim extensionality
-- bcong : ∀ {X Y} {xs ys : Stream X} → (f : Stream X → Stream Y) → Bisimilar xs ys → Bisimilar (f xs) (f ys)
-- head (bcong f Z) = {!head Z!}
-- tail (bcong f Z) = {!!}


-------------------------------------
-- Properties of Stream Operations --
-------------------------------------



map-bisim : ∀ {X Y} {xs ys : Stream X} → {f : X → Y} → xs ~ ys → (map f xs) ~ (map f ys)
head (map-bisim {f = f} Z) = cong f (head Z)
tail (map-bisim Z) = map-bisim (tail Z)

-- If 2 streams are bisimilar, next finds the same thing in both
next-eq : {X : Set} {P : X → Set} {xs ys : Stream X} → (pxs : Eventually P xs) (pys : Eventually P ys)
        → xs ~ ys
        → next pxs ≡ next pys
next-eq (here px) (here py) Z = head Z
next-eq {P = P} (here px) (there ¬py pys) Z = ⊥-elim (¬py (subst P (head Z) px))
next-eq {P = P} (there ¬px pxs) (here py) Z = ⊥-elim (¬px (subst P (sym $ head Z) py))
next-eq (there ¬px pxs) (there ¬py pys) Z = next-eq pxs pys (tail Z)

-- -- This version is too strong to be useful that often, since the input streams won't always be bisimilar, even when the outputs are
-- filter-bisim : {X : Set} {P : X → Set} → {xs ys : Stream X} → {pxs : Always (Eventually P) xs} {pys : Always (Eventually P) ys}
--              → xs ~ ys
--              → filter' pxs ~ filter' pys
-- head (filter-bisim {pxs = pxs} {pys} Z) = dcong₂ _,_ (next-eq (now pxs) (now pys) Z) {!!}
-- tail (filter-bisim {pxs = pxs} {pys} Z) = filter-bisim (tail Z)

-- We don't need to insist on xs~ys - instead, we can just ask for weak bisimilarity of the AE proofs
filter-wbisim : {X : Set} {P : X → Set} → {xs ys : Stream X} → {pxs : Always (Eventually P) xs} {pys : Always (Eventually P) ys}
             → WBisimilar P pxs pys
             → filter' pxs ~ filter' pys
head (filter-wbisim {X} {P} {xs} {ys} {pxs} {pys} Z) = EqNexts.eq-next (now Z)
tail (filter-wbisim {X} {P} {xs} {ys} {pxs} {pys} Z) = filter-wbisim (forever Z)

---------------
-- Unfolding --
---------------

--  It'd be great to define unfolding like so, except the termination checker
--  rejects it for lack of guardedness:
private module _ where
  -- Inside a private submodule so we don't accidentally try to use it
  {-# TERMINATING #-} -- uncomment if ye dare
  unfold-i-wish : ∀ {X n} → (Γ : Ctx X n) → RStream X n → Stream X
  unfold-i-wish Γ (loop x) = unfold-i-wish Γ (lookup Γ x)
  unfold-i-wish Γ (cons x xs) = x ∷ (unfold-i-wish (Γ -, cons x xs) xs)

-- So let's do it in a slightly more roundabout way.

-- We can unfold RStream to a Stream, so long as we leave in dummies where the variables were.
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

unfold-wbisim : ∀ {X n} (Γ : Ctx X n) (x : Fin n)
              → WBisimilar Is-just (unfold-productive Γ (loop x)) (unfold-productive Γ (lookup Γ x))
now (unfold-wbisim Γ x) = {!!}
forever (unfold-wbisim Γ x) = {!!}

-- Put the pieces together to get the real unfolding.
-- Except we dont want to reason (or even know) about that roundabout definition, so
-- we make it opaque and prove the defining equations we wanted in the first place as lemmas.
opaque
  unfold : ∀ {X n} → (Γ : Ctx X n) → RStream X n → Stream X
  unfold Γ xs = remove-dummies (unfold-productive Γ xs)

  unfold-loop' : ∀ {X n} → (Γ : Ctx X n) → (x : Fin n) → (unfold Γ (loop x)) ~ (unfold Γ (lookup Γ x))
  unfold-loop' Γ x = map-bisim (filter-wbisim (unfold-wbisim Γ x))

  unfold-loop : ∀ {X n} → (Γ : Ctx X n) → (x : Fin n) → unfold Γ (loop x) ≡ unfold Γ (lookup Γ x)
  unfold-loop = {!!} -- via bisim extensionality

  unfold-cons : ∀ {X n} → (Γ : Ctx X n) → (x : X) (xs : RStream X (suc n)) → unfold Γ (cons x xs) ≡ x ∷ (unfold (Γ -, cons x xs) xs)
  unfold-cons = {!!}

-----------
-- Loops --
-----------

-- An RStream is a loop if it loops back to the very start.
-- NB: This is not preserved by weakening.
IsLoop : ∀ {X} {n : ℕ} → RStream X n → Set
IsLoop (loop x) = IsMax x
IsLoop (cons x l) = IsLoop l

-- As long as we know how far we've come, and that we've made at least some progress by the time we reach the end,
-- we can fold the list into a loop.
loopify' : ∀ {X c} → (n : ℕ) → (xs : Vec X c) → (Zero c → NonZero n) → RStream X n
loopify' n [] p with p zero
loopify' (suc n) [] p | n' = loop (F.fromℕ n)
loopify' n (x ,- xs) p = cons x (loopify' (suc n) xs (const nonZero))

loopify : ∀ {X c} (xs : Vec X c) → {{_ : NonZero c}} → RStream X 0
loopify xs {{nz}} = loopify' 0 xs (λ z → ⊥-elim (¬Z&NZ (z , nz)))

loopify-isloop : ∀ {X c} n (xs : Vec X c) p → IsLoop (loopify' n xs p)
loopify-isloop n [] p with p zero
loopify-isloop (suc n) [] p | n' = fromℕ-ismax n
loopify-isloop n (x ,- xs) p = loopify-isloop (suc n) xs _

-- -- On the other hand, if we're given the looping segment, we can repeat it infinitely to get a stream directly.
-- -- The index n of the vector is one of the divisors.
-- repeatω' : ∀ {X n m} → Vec X n → Vec X m → Stream X
-- repeatω' original [] = repeatω' original original
-- repeatω' original (x ,- xs) = x ∷ (repeatω' original xs)

-------------------------
-- Algebraic Structure --
-------------------------

-- Two operations: unrolling, and loosening.
-- If two RStreams can be equalised by applications of these, then they
-- represent the same stream (ie, are bisimilar).


-- first, a definition on vectors.
-- And they all rolled over and one fell out...
rotate : ∀ {X : Set} {n} → Vec X n → Vec X n
rotate [] = []
rotate {n = suc n} (x ,- xs) rewrite +-comm 1 n = xs <<< (x ,- [])

-- Add a finite prefix to the front of an RStream.
-- Inefficient due to repeated traversals, but meh.
extend : ∀ {X : Set} {p n} → Vec X p → RStream X n → RStream X n
extend [] ys = ys
extend (x ,- xs) ys = cons x (extend xs (rescope F.suc ys))

-- We can view an RStream as a "lasso" - a finite prefix, and a nonempty looping section.
-- The explicit separation removes the need for a variable
record Lasso (X : Set) (|prefix| : ℕ) (|cycle| : ℕ) {{_ : NonZero |cycle|}} : Set where
  constructor _-∘_
  field
    prefix : Cev X |prefix|
    cycle  : Vec X |cycle|

  unroll : Lasso X (suc |prefix|) |cycle|
  prefix unroll = prefix -, V<.head-nz cycle
  cycle unroll = rotate cycle

  loosen : (k : ℕ) {{_ : NonZero k}} → Lasso X |prefix| (k * |cycle|) {{m*n≢0 _ _}}
  prefix (loosen k) = prefix
  cycle (loosen k) = V<.repeat k cycle

  toRStream : RStream X 0
  toRStream = extend (V>.rev prefix) (loopify cycle)

open Lasso

-- split rstream intp prefix and loop, for which the other view of RStreams would be *lovely*
toLasso : ∀ {X n p c} {{_ : NonZero c}} →  RStream X n → Lasso X p c
toLasso = {!!}

unfold-lasso : ∀ {X p c} {{_ : NonZero c}} → Lasso X p c → Stream X
unfold-lasso = unfold [] ∘ toRStream


data LAction : Set where
  `unroll` : LAction
  `loosen` : (k : ℕ) {{_ : NonZero k}} → LAction

exec : ∀ {X p c} {{_ : NonZero c}} → LAction → Lasso X p c → ∃[ p' ] ∃[ c' ] ∃[ nzc' ] Lasso X p' c' {{nzc'}}
exec `unroll` xs = _ , _ , _ , unroll xs
exec (`loosen` k) xs = _ , _ , _ , loosen xs k

exec-all : ∀ {X p c} {{_ : NonZero c}} → List LAction → Lasso X p c → ∃[ p' ] ∃[ c' ] ∃[ nzc' ] Lasso X p' c' {{nzc'}}
exec-all [] xs = _ , _ , _ , xs
exec-all (a ∷ as) xs with exec a xs
... | (p , c , nz , xs') = exec-all {p = p} {c} {{nz}} as xs'

-- Bisimiliarity of lassos - there exists some sequence of loosenings and unrollings that equalise the lassos
_≈_ : {X : Set} {p p' c c' : ℕ} {{_ : NonZero c}} {{_ : NonZero c'}}
    → Lasso X p c → Lasso X p' c' → Set
xs ≈ ys = Σ[ as ∈ List LAction ] Σ[ bs ∈ List LAction ] (exec-all as xs ≡ exec-all bs ys)


------------------------------------
-- Proving Bisimilarity of Lassos --
------------------------------------

-- If two lassos are equal, then they are bisimilar

-- Unrolling preserves bisimulation

-- Loosening preserves bisimulation

-- The big one: if there exists two sequences of loosening and unrolling which equalise the lassos, then they must have been bisimiar.


-- "Bisimilarity" of lassos implies stream bisimilarity of their unfoldings
≈→~ : ∀ {X p p' c c'} {{_ : NonZero c}} {{_ : NonZero c'}}
        → (xs : Lasso X p c) (ys : Lasso X p' c')
        → xs ≈ ys → (unfold-lasso xs) ~ (unfold-lasso ys)
≈→~ xs ys (as , bs , eq) with exec-all as xs | exec-all bs ys
≈→~ xs ys (as , bs , refl) | xs' | .xs' = record { head = {!!} ; tail = {!!} }


--------------------------------------
-- Proof that sqrt(2) is Irrational --
--------------------------------------

Digit = Fin 10

-- The unit interval of real numbers [0,1].
-- The stream contains the digits right of the decimal point.
I = Stream Digit


