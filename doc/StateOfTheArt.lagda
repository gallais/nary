\begin{code}
{-# OPTIONS --safe --without-K #-}

open import Relation.Nullary

open import Level using (Level)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (_,_)
open import Relation.Unary
open import Function

private
  variable
    a b c p q r : Level
    A : Set a
    B : Set b
    C : Set c
    P : A → Set p
    Q : A → Set q
    R : A → Set r

satisfiable : ∃⟨ All P ⟩
satisfiable = [] , []

zip : ∀[ All P ⇒ All Q ⇒ All (P ∩ Q) ]
zip []        []        = []
zip (x ∷ xs)  (y ∷ ys)  = (x , y) ∷ zip xs ys

replicate : ∀[ P ] → Π[ All P ]
replicate f []        = []
replicate f (x ∷ xs)  = f ∷ replicate f xs

open import Data.Nat.Base
open import Relation.Binary.PropositionalEquality

private
  variable
    m n : ℕ

antisym : ∀[ (m ≥_) ⇒ (m ≤_) ⇒ (m ≡_) ]
antisym z≤n        z≤n        = refl
antisym (s≤s m≥n)  (s≤s m≤n)  = cong suc (antisym m≥n m≤n)



\end{code}
