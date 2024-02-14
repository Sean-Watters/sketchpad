{-# OPTIONS --safe #-}

open import Function.Base using (_∘_)
open import Data.Unit.Base using (⊤; tt)

module bug where

record WTy : Set

TyFwd : WTy

data WExpBase : WTy → Set

record WTy where
  -- inductive
  constructor Is
  field
    inner : WExpBase TyFwd

WExp : WExpBase TyFwd → Set
WExp = WExpBase ∘ Is


data WExpBase where
  Ty    : WExpBase TyFwd
  _-_  : WExpBase TyFwd → WExpBase TyFwd → WExpBase TyFwd

TyFwd = Is Ty

infixr 1 _-_

foo : ∀ {a} → WExp a → ⊤
foo Ty = tt
