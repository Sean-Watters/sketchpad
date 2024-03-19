module Bug.AbstractShow where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.String

opaque
  foo : Nat → Nat
  foo n = n + 5

show : Nat → String
show n = primShowNat (foo n)

test : show 0 ≡ "5"
test = {!refl!}  -- stuck on abstract as expected

_ = {!0!} -- fully normalises to 5, seeing through the abstract block
