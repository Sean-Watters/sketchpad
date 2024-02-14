{-# OPTIONS --safe #-}
module CoStream where

open import Data.Nat
open import Data.Empty

-- List A     := μX.1+(A×X) -- genuinely finite
-- CoList A   := νX.1+(A×X) -- maybe finite, maybe infinite
-- Stream A   := νX.A×X     -- genuinely infinite
-- CoStream A := μX.A×X     -- suspicious...

-- We can say what a CoStream ought to be:
data CoStream (A : Set) : Set where
  _∷_ : A → CoStream A → CoStream A

infixr 10 _∷_

-- But it's more than a little bit difficult to make one!
-- We can go for a while, but we never get to finish.
foo : CoStream ℕ
foo = 0 ∷ 1 ∷ 2 ∷ {!!}

-- If we allow pattern matching on CoStream with the `pattern` keyword,
-- then we can prove that it is uninhabited by induction:
empty : ∀ {A} → CoStream A → ⊥
empty (x ∷ xs) = empty xs

