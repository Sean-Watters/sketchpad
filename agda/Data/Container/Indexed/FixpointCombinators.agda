{-# OPTIONS --safe #-}

module Data.Container.Indexed.FixpointCombinators where

open import Level
open import Data.Unit
open import Data.Container.Indexed
open import Data.Container.Combinator using ()
open import Data.Sum
open import Data.W.Indexed
open import Data.Product

open import Axiom.Extensionality.Propositional
open import Relation.Binary.Isomorphism
open import Relation.Binary.PropositionalEquality

-- applying the pow fam flip to containers
fromSP : ∀ {ℓo ℓs ℓp} {I : Set ℓp} {O : Set ℓo}
       → (S : O → Set ℓs) (P : {o : O} → S o → I → Set ℓp)
       → Container I O ℓs ℓp
fromSP {I = I} {O = O} S P = S ◃ (λ x → Σ[ i ∈ I ] (P x i)) / λ c x → proj₁ x

toSP : ∀ {ℓo ℓs ℓp} {I : Set ℓp} {O : Set ℓo}
     → Container I O ℓs ℓp
     → Σ[ S ∈ (O → Set ℓs) ] ({o : O} → S o → I → Set ℓp)
toSP {I = I} {O = O} (C ◃ R / n) = C , λ c i → Σ[ x ∈ R c ] (n c x ≡ i)

module _ (ℓ : Level) (I : Set ℓ) (O : Set ℓ) where

  -- Instructive step; partial application of containers
  _[_]C : Container (I ⊎ O) ⊤ ℓ ℓ
        → Container I O ℓ ℓ
        → Container I ⊤ ℓ ℓ
  (C1 ◃ R1 / n1) [ C2 ◃ R2 / n2 ]C
    = ⟦_⟧ {I = O} {⊤} (C1 ◃ (λ c → Σ[ o ∈ O ] Σ[ r ∈ R1 c  ] (n1 c r ≡ (inj₂ o))) / λ _ → proj₁) C2
    ◃ {!!}
    / {!!}


  -- Shapes of Mu's are trees, and positions are paths through
  -- the tree which terminate at leaf positions.

  -- The type we actually want, I think?
  -- data Path (C : Container (I ⊎ O) O ℓs ℓp) : (o : O) → {!W!} → I → Set (ℓs ⊔ ℓp) where

  data Path (C : O → Set ℓ)
            (R : {o : O} → C o → Set ℓ) -- having the same R for both may be suspicious?
            (ni : {o : O} → (c : C o) → R c → I)
            (no : {o : O} → (c : C o) → R c → O)
            : {o : O} → W (C ◃ R / no) o → I → Set ℓ where


  Mu : Container (I ⊎ O) O ℓ ℓ → Container I O ℓ ℓ
  Mu = {!!}
