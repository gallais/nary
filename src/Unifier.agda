{-# OPTIONS --allow-unsolved-metas #-}

module Unifier where

open import Data.Nat.Base using (ℕ; zero; suc)
open import StateOfTheArt
  using ( _×_; ⊤
        ; _,_
        ; _≡_; refl
        )


_ : _
_ = _




_ : (_ → _) ≡ (ℕ → ℕ)
_ = refl




_ : let ?A = _ in (?A → ?A) ≡ (ℕ → ℕ)
_ = refl



_ : (ℕ → _) ≡ (ℕ → ℕ)
_ = refl



_ : _ ≡ (_ → _)
_ = refl


private
  variable
    A : Set


nary : ℕ → Set → Set
nary zero     A = A
nary (suc n)  A = ℕ → nary n A



at0 : ∀ n → nary n A → A
at0 zero    f = f
at0 (suc n) f = at0 n (f 0)




_ : nary 1 _ ≡ (ℕ → ℕ)
_ = refl



_ : nary 0 _ ≡ (ℕ → ℕ)
_ = refl



_ : nary _ _ ≡ (ℕ → A)
_ = refl



_ : nary _ ℕ ≡ ℕ
_ = refl

_ : nary _ ℕ ≡ (ℕ → ℕ)
_ = refl

_ : nary _ (ℕ → ℕ) ≡ (ℕ → ℕ)
_ = refl
