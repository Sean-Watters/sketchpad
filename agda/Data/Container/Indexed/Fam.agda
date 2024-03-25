{-# OPTIONS --cubical-compatible --sized-types #-}

module Data.Container.Indexed.Fam where

-- The standard library uses so-called "pow-style" indexed
-- containers, where all the positions ("responses") live 
-- in one set, and you get a "next" function for picking out
-- their indices. This makes taking fixed points much harder, so
-- we instead use the "fam-style" presentation of Altenkirch et al,
-- with an indexed familty of positions.

open import Level using (Level) renaming (suc to lsuc)
open import Size
open import Codata.Sized.Thunk using (Thunk; force)
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Function hiding (force)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Relation.Binary.Isomorphism

----------
-- Base --
----------

-- Indexed containers, fam style
record Container (I J : Set) : Set₁ where
  constructor _◃_
  field
    Shape : J → Set
    Position : {j : J} → Shape j → I → Set
open Container

-- The meaning/extension of a container is the indexed functor that it represents.
⟦_⟧ : {I J : Set} → Container I J → (I → Set) → (J → Set)
⟦ S ◃ P ⟧ F j = Σ[ s ∈ S j ] (∀ {i} → P s i → F i)

-- Indexed W-types. AKA how to generate families of inductive data types
-- from indexed containers.
-- W-types are trees with node arity given by the set of shapes, and
data W {J : Set} (C : Container J J) : J → Set where
  sup : ∀ {j} → ⟦ C ⟧ (W C) j → W C j


-- Indexed M-types.
-- Dual to W-types; so this is the way to generate families of
-- coinductive codata types from indexed containers.
-- In general we get possibly-infinite trees.
data M {J : Set} (C : Container J J) (κ : Size) : J → Set where
  inf :  ∀ {j} → ⟦ C ⟧ (λ j' → Thunk (λ α → M C α j) κ) j → M C κ j


------------------------
-- Functoriality in I --
------------------------

⟨map⟩ : {I I' J : Set} → (I' → I) → Container I J → Container I' J
⟨map⟩ f (S ◃ P) = S ◃ (λ s i' → P s (f i'))

-----------------
-- Combinators --
-----------------

private
  variable
    I J : Set

-- The Identity Container.

⟨id⟩ : Container J J
⟨id⟩ = const ⊤ ◃ λ {i} _ j → i ≡ j

-- The Constant Container.

⟨const⟩ : (J → Set) → Container I J
⟨const⟩ P = P ◃ (const (const ⊥))

-- Binary Product.
-- Shapes are pairs of shapes from the left and right;
-- Positions are a *choice* of a left position or a right position.

_⟨×⟩_ : Container I J → Container I J → Container I J
(S ◃ P) ⟨×⟩ (T ◃ Q) = (λ j → S j × T j)
                    ◃ (λ x i → (P (proj₁ x) i) ⊎ (Q (proj₂ x) i))

-- Indexed Product.
-- Generalisation of binary product to indexing sets other than Bool.
-- And in fact, to indexing sets which are dependent on J.

⟨Π⟩ : {X : J → Set} → (∀ {j} → X j → Container I J) → Container I J
⟨Π⟩ {X = X} P = (λ j → (x : X j) → Shape (P x) j)
              ◃ (λ {j} Q i → Σ[ x ∈ X j ] Position (P x) (Q x) i )

-- The version where the product is indexed by a simple type X
-- ⟨Π⟩ : {X : Set} → (X → Container I J) → Container I J
-- ⟨Π⟩ {X = X} P = (λ j → (x : X) → Shape (P x) j)
--               ◃ (λ Q i → Σ[ x ∈ X ] Position (P x) (Q x) i )

-- Binary Sum.
-- Shapes are either a shape from the left or right.
-- The choice of shape *determines* where you must take a position from.

_⟨+⟩_ : Container I J → Container I J → Container I J
(S ◃ P) ⟨+⟩ (T ◃ Q) = (λ j → S j ⊎ T j)
                    ◃ [ P , Q ]

-- Indexed Sum.
-- Generalisation of binary sum to arbirary indexing sets (possibly
-- dependent on J)


⟨Σ⟩ : {X : J → Set} → (∀ {j} → X j → Container I J) → Container I J
⟨Σ⟩ {X = X} P = (λ j → Σ[ x ∈ X j ] Shape (P x) j)
              ◃ (λ { (x , s) i → Position (P x) s i })

-- The version where X is a simple type
-- ⟨Σ⟩ : {X : Set} → (X → Container I J) → Container I J
-- ⟨Σ⟩ {X = X} P = (λ j → Σ[ x ∈ X ] Shape (P x) j)
--               ◃ (λ { (x , s) i → Position (P x) s i })


--------------------
-- Least Fixpoint --
--------------------

data Path {I J : Set}
          (S : J → Set)
          (PI : {j : J} → S j → I → Set)
          (PJ : {j : J} → S j → J → Set)
          : {j : J} → W (S ◃ PJ) j → I → Set where
  path : {j : J} {s : S j} {f : {j : J} → PJ s j → W (S ◃ PJ) j} {i : I}
       → PI s i
       ⊎ (Σ[ j' ∈ J ] Σ[ p ∈ PJ s j' ] Path S PI PJ (f p) i)
       → Path S PI PJ (sup (s , f)) i

⟨μ⟩ : {I J : Set} →  Container (I ⊎ J) J → Container I J
⟨μ⟩ {I} {J} (S ◃ P) =
  let PI : {j : J} → S j → I → Set
      PI s i = P s (inj₁ i)

      PJ : {j : J} → S j → J → Set
      PJ s j = P s (inj₂ j)

  in (W (S ◃ PJ)) ◃ Path S PI PJ


-----------------------
-- Greatest Fixpoint --
-----------------------

-- M-types are possibly infinite trees, so paths through them are co-lists
data CoPath {I J : Set}
            (S : J → Set)
            (PI : {j : J} → S j → I → Set)
            (PJ : {j : J} → S j → J → Set)
            (κ : Size)
            : {j : J} → M (S ◃ PJ) κ j → I → Set where
  copath : {j : J} {s : S j} {f : {j' : J} → PJ s j' → Thunk (λ α → M (S ◃ PJ) α j) ∞} {i : I}
         → PI s i
         ⊎ (Σ[ j' ∈ J ] Σ[ p ∈ PJ s j' ] CoPath S PI PJ κ (force (f p)) i)
         → CoPath S PI PJ κ (inf (s , f)) i

⟨ν⟩ : {I J : Set} → Container (I ⊎ J) J → Container I J
⟨ν⟩ {I} {J} (S ◃ P) =
  let PI : {j : J} → S j → I → Set
      PI s i = P s (inj₁ i)

      PJ : {j : J} → S j → J → Set
      PJ s j = P s (inj₂ j)

  in M (S ◃ PJ) ∞ ◃ CoPath S PI PJ ∞
