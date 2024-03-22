{-# OPTIONS --safe --guardedness --with-K #-}
module CoData.OrdinalSizedTypes where

open import Level
open import Data.Unit using (⊤)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
open import Data.Sum

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])


data T : Set where
  * : T
  _^+_ : T → T → T

_≟_ : (x y : T) → Dec (x ≡ y)
* ≟ * = yes refl
* ≟ (x ^+ y) = no (λ ())
(x ^+ y) ≟ * = no (λ ())
(x ^+ y) ≟ (x' ^+ y') with x ≟ x' | y ≟ y'
... | yes refl | yes refl = yes refl
... | no ¬p | _ = no λ {refl → ¬p refl}
... | _ | no ¬p = no λ {refl → ¬p refl}

data _<_ : T → T → Set where
  z : ∀ {a b}     → * < (a ^+ b)
  l : ∀ {a b c d} → a < c → (a ^+ b) < (c ^+ d)
  r : ∀ {a b d}   → b < d → (a ^+ b) < (a ^+ d)

_≤_ : T → T → Set
x ≤ y = (x < y) ⊎ (x ≡ y)

left : T → T
left * = *
left (x ^+ y) = x

data isCNF : T → Set where
  z : isCNF *
  n : ∀ {x y} → isCNF x → isCNF y → (left y) ≤ x → isCNF (x ^+ y)

-- Type of ordinals realised as Cantor Normal Forms,
-- which we use as size indices.
Size : Set
Size = Σ[ t ∈ T ] (isCNF t)

_<'_ : Size → Size → Set
x <' y = proj₁ x < proj₁ y

--------------------
-- Key Properties --
--------------------

<-irrefl : ∀ {t} → ¬ (t < t)
<-irrefl {a ^+ b} (l x) = <-irrefl x
<-irrefl {a ^+ b} (r x) = <-irrefl x

<-prop : ∀ {s t} → (p q : s < t) → p ≡ q
<-prop z z = refl
<-prop (l p) (l q) = cong l (<-prop p q)
<-prop (l p) (r q) = ⊥-elim (<-irrefl p)
<-prop (r p) (l q) = ⊥-elim (<-irrefl q)
<-prop (r p) (r q) = cong r (<-prop p q)

≤-prop : ∀ {s t} → (p q : s ≤ t) → p ≡ q
≤-prop (inj₁ x) (inj₁ y) = cong inj₁ (<-prop x y)
≤-prop (inj₁ x) (inj₂ refl) = ⊥-elim (<-irrefl x)
≤-prop (inj₂ refl) (inj₁ y) = ⊥-elim (<-irrefl y)
≤-prop (inj₂ refl) (inj₂ refl) = refl -- requires K!

isCNF-prop : ∀ {t} → (x y : isCNF t) → x ≡ y
isCNF-prop z z = refl
isCNF-prop (n tx ty p) (n sx sy q)
  rewrite isCNF-prop tx sx
  rewrite isCNF-prop ty sy
  rewrite ≤-prop p q
  = refl

eq-Size : { x y : Size } → proj₁ x ≡ proj₁ y → x ≡ y
eq-Size {.y , px} {y , py} refl = cong (y ,_) (isCNF-prop px py)

--------------------
-- Size Constants --
--------------------

0t : T
0t = *

0s : Size
0s = 0t , z

1t : T
1t = 0t ^+ 0t

1s : Size
1s = 1t , n z z (inj₂ refl)

ωt : T
ωt = 1t ^+ 0t

ωs : Size
ωs = ωt , n (n z z (inj₂ refl)) z (inj₁ z)

----------------------
-- Size Combinators --
----------------------

suct : T → T
suct * = 1t
suct (x ^+ y) = x ^+ suct y

left≡left∘suct : ∀ t → left (suct t) ≡ left t
left≡left∘suct * = refl
left≡left∘suct (x ^+ y) = refl

suct-isCNF : ∀ {t} → isCNF t → isCNF (suct t)
suct-isCNF z = n z z (inj₂ refl)
suct-isCNF {x ^+ y} (n px py q) = n px (suct-isCNF py) (subst (_≤ x) (sym (left≡left∘suct y)) q)

sucs : Size → Size
sucs (t , p) = suct t , suct-isCNF p

-----------------------------------------------------
-- Sized Sets and their use in guarded coinduction --
-----------------------------------------------------

-- SizedSets are sets indexed by their (possibly
-- transfinite) sizes
SizedSet : ∀ ℓ → Set (suc ℓ)
SizedSet ℓ = Size → Set ℓ

record Thunk {ℓ} (F : SizedSet ℓ) (i : Size) : Set ℓ where
  constructor delay
  coinductive
  field force : {j : Size} (j<i : j <' i) → F j

