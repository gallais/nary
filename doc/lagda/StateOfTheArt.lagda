\begin{code}
{-# OPTIONS --safe --without-K #-}

open import Data.Empty
open import Level using (Level; _⊔_)
open import Function

private
  variable
    a b c p q r i : Level
    A : Set a
    B : Set b
    C : Set c
    I : Set i
    P : A → Set p
    Q : A → Set q
    R : A → Set r

\end{code}
%<*list>
\begin{code}
data List (A : Set a) : Set a where
  []   : List A
  _∷_  : A → List A → List A
\end{code}
%</list>
\begin{code}

\end{code}
\begin{code}
module _ {I : Set i} where
\end{code}
%<*iuniversal>
\begin{code}
  ∀[_] : (I → Set p) → Set (i ⊔ p)
  ∀[ P ] = ∀ {i} → P i
\end{code}
%</iuniversal>
\begin{code}


private
  variable
    x y : A
    xs ys : List A

module _ {A : Set a} where

\end{code}
%<*all>
\begin{code}
  data All (P : A → Set p) : List A → Set (a ⊔ p) where
    []   : All P []
    _∷_  : P x → All P xs → All P (x ∷ xs)
\end{code}
%</all>
\begin{code}

\end{code}
%<*any>
\begin{code}
  data Any (P : A → Set p) : List A → Set (a ⊔ p) where
    [_]  : P x → Any P (x ∷ xs)
    _∷_  : ∀ x → Any P xs → Any P (x ∷ xs)
\end{code}
%</any>
\begin{code}

  infix 10 ∃⟨_⟩
\end{code}
%<*exists>
\begin{code}
  record ∃⟨_⟩ (P : A → Set p) : Set (a ⊔ p) where
    constructor _,_
    field witness   : A
          property  : P witness
\end{code}
%</exists>
\begin{code}


infixr 9 _⇒_
\end{code}
%<*implies>
\begin{code}
_⇒_ : (I → Set p) → (I → Set q) → (I → Set (p ⊔ q))
(P ⇒ Q) i = P i → Q i
\end{code}
%</implies>
\begin{code}

\end{code}
%<*ap>
\begin{code}
_<⋆>_ : ∀[ All (P ⇒ Q) ⇒ All P ⇒ All Q ]
[]        <⋆> []        = []
(f ∷ fs)  <⋆> (x ∷ xs)  = f x ∷ (fs <⋆> xs)
\end{code}
%</ap>
\begin{code}

infix 10 ¬_
\end{code}
%<*negation>
\begin{code}
¬_ : (I → Set p) → (I → Set p)
(¬ P) i = P i → ⊥
\end{code}
%</negation>
\begin{code}


\end{code}
%<*none>
\begin{code}
none : ∀[ ¬ P ] → ∀[ ¬ Any P ]
none ¬p [ px ]    = ¬p px
none ¬p (x ∷ px)  = none ¬p px
\end{code}
%</none>
\begin{code}


\end{code}
%<*any>
\begin{code}
fromAll : ∀[ Any Q ⇒ All P ⇒ Any P ]
fromAll _ (px ∷ _) = [ px ]
\end{code}
%</any>

\end{code}
%<*satisfiable>
\begin{code}
satisfiable : ∃⟨ All P ⟩
satisfiable = [] , []
\end{code}
%</satisfiable>
\begin{code}

module _ {I : Set i} where
\end{code}
%<*universal>
\begin{code}
  Π[_] : (I → Set p) → Set (i ⊔ p)
  Π[ P ] = ∀ i → P i
\end{code}
%</universal>
\begin{code}

\end{code}
%<*replicate>
\begin{code}
replicate : ∀[ P ] → Π[ All P ]
replicate p []        = []
replicate p (x ∷ xs)  = p ∷ replicate p xs
\end{code}
%</replicate>
\begin{code}

\end{code}
%<*map>
\begin{code}
map : ∀[ P ⇒ Q ] → ∀[ All P ⇒ All Q ]
map f []          = []
map f (px ∷ pxs)  = f px ∷ map f pxs
\end{code}
%</map>
\begin{code}

open import Data.Nat.Base
open import Relation.Binary.PropositionalEquality

private
  variable
    m n : ℕ

\end{code}
%<*brokenantisym>
\begin{code}
asym : ∀[ (m ≥_) ⇒ (m ≤_) ⇒ (m ≡_) ]
asym z≤n        z≤n        = refl
asym (s≤s m≥n)  (s≤s m≤n)  = cong suc (asym m≥n m≤n)
\end{code}
%</brokenantisym>
\begin{code}


\end{code}
