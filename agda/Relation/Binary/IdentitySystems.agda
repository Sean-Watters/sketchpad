{-# OPTIONS --cubical-compatible #-}
module Relation.Binary.IdentitySystems where

open import Level


module Unbased where
  data Id {ℓ : Level} {X : Set ℓ} : X → X → Set ℓ where
    refl : ∀ {x} → Id x x

  J-Rule : ∀ {ℓ} {X : Set ℓ} (P : (x y : X) → Id x y → Set) → Set ℓ
  J-Rule {X = X} P = (∀ (c : X) → P c c refl)
                   → (∀ (a b : X) (eq : Id a b) → P a b eq)

  K-Rule : ∀ {ℓ} {X : Set ℓ} (P : (x : X) → Id x x → Set) → Set ℓ
  K-Rule {X = X} P = (∀ (c : X) → P c refl)
                   → (∀ (a : X) (eq : Id a a) → P a eq)

  K⇒J : (∀ {ℓ} {X : Set ℓ} (P : (x : X) → Id x x → Set) → K-Rule P)
      → (∀ {ℓ} {X : Set ℓ} (P : (x y : X) → Id x y → Set) → J-Rule P)
  K⇒J K P f a b eq = {!K!}



  J : ∀ {ℓ} {X : Set ℓ} (P : (x y : X) → Id x y → Set)
    → J-Rule P
  J P f a b refl = f a

  K : ∀ {ℓ} {X : Set ℓ} (P : (x : X) → Id x x → Set)
    → K-Rule P
  K P x a eq = {!!}

module Based where
  data Id {ℓ : Level} {X : Set ℓ} (a : X) : X → Set ℓ where
    refl : Id a a

Based⇒Unbased : ∀ {ℓ} {X : Set ℓ} {a b : X} → Based.Id a b → Unbased.Id a b
Based⇒Unbased Based.refl = Unbased.refl

Unbased⇒Based : ∀ {ℓ} {X : Set ℓ} {a b : X} → Based.Id a b → Unbased.Id a b
Unbased⇒Based Based.refl = Unbased.refl
