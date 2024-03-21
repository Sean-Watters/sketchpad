{-# OPTIONS --safe --cubical-compatible --guardedness #-}

module Data.Container.Indexed.Fam.Base where

open import Level using (Level) renaming (suc to lsuc)
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum


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

⟦_⟧ : {I J : Set} → Container I J → (I → Set) → (J → Set)
⟦ S ◃ P ⟧ F j = Σ[ s ∈ S j ] (∀ {i} → P s i → F i)

-- Indexed W-types for them.
data W {J : Set} (C : Container J J) : J → Set where
  sup : ∀ {j} → ⟦ C ⟧ (W C) j → W C j


-- Indexed M-types.
-- Following the standard library, the extension of the container is
-- inlined into the coninductive definition.
-- Niu & Spivak's "Positions and Angles" terminology works a bit better
-- in this presentation than AAG's "Shapes and Positions";
-- In this presentation, we think of our "shapes" as a set of ways to
-- root the tree, and our positions as "directions" in which subtrees
-- extend.
-- Honestly, this way of thinking was more instructive to me than the
-- traditional setup of ⟦_⟧ and W above.
record M {J : Set} (C : Container J J) : Set where
  coinductive
  constructor inf
  field
    root   : (j : J) → Shape C j -- Choose a shape to root the tree with...
    branch : ∀ {j} → Position C (root j) j → M C -- Then for every position, we have a further subtree

-- TODO: this is wrong, we really do need *indexed* M-types. See CoVec for an
-- example of how to do indexed codata


-----------------
-- Combinators --
-----------------

private
  variable
    I J : Set

-- The Identity Container.

⟨id⟩ : Container J J
⟨id⟩ = (λ _ → ⊤) ◃ λ _ _ → ⊥

-- The Constant Container.

⟨const⟩ : (J → Set) → Container I J
⟨const⟩ P = P ◃ λ _ _ → ⊥

-- Binary Product.
-- Shapes are pairs of shapes from the left and right;
-- Positions are a *choice* of a left position or a right position.

_⟨×⟩_ : Container I J → Container I J → Container I J
(S ◃ P) ⟨×⟩ (T ◃ Q) = (λ j → S j × T j)
                    ◃ (λ x i → (P (proj₁ x) i) ⊎ (Q (proj₂ x) i))

-- Indexed Product.
-- Generalisation of binary product to index sets other than 𝟚.

⟨Π⟩ : {X : Set} → (X → Container I J) → Container I J
⟨Π⟩ {X = X} P = (λ j → (x : X) → Shape (P x) j)
              ◃ (λ Q i → Σ[ x ∈ X ] Position (P x) (Q x) i )

-- Binary Sum.
-- Shapes are either a shape from the left or right.
-- The choice of shape *determines* where you must take a position from.

_⟨+⟩_ : Container I J → Container I J → Container I J
(S ◃ P) ⟨+⟩ (T ◃ Q) = (λ j → S j ⊎ T j)
                    ◃ [ P , Q ]

-- Indexed Sum.
-- Generalisation of binary sum to index sets other than 𝟚.

⟨Σ⟩ : {X : Set} → (X → Container I J) → Container I J
⟨Σ⟩ {X = X} P = (λ j → Σ[ x ∈ X ] Shape (P x) j)
              ◃ (λ { (x , s) i → Position (P x) s i })


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


record CoPath {I J : Set}
              (S : J → Set)
              (PI : {j : J} → S j → I → Set)
              (PJ : {j : J} → S j → J → Set) : Set where
              -- : {j : J} → W (S ◃ PJ) j → I → Set where
  coinductive
  constructor copath
  field
    head : {!!}
    tail : {!!}

⟨ν⟩ : {I J : Set} → Container (I ⊎ J) J → Container I J
⟨ν⟩ {I} {J} (S ◃ P) =
  let PI : {j : J} → S j → I → Set
      PI s i = P s (inj₁ i)

      PJ : {j : J} → S j → J → Set
      PJ s j = P s (inj₂ j)

  in {!M (S ◃ PJ)!} ◃ {!!}
