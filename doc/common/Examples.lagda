\begin{code}
{-# OPTIONS --without-K --safe #-}

module Examples where

open import Level using (Level; _⊔_)
open import StateOfTheArt as SOA
  hiding ( ∃⟨_⟩; ∀[_]; Π[_]; _⇒_; _∩_; ¬_
         ; _<⋆>_
         )

private
  variable
    a b r s p : Level
    A : Set a
    B : Set b
    R : A → B → Set r
    S : A → B → Set s

------------------------------------------------------------------------
-- Introduction
------------------------------------------------------------------------

-- Data.Product.N-ary.Heterogeneous provides a generic representation of
-- n-ary heterogeneous (non dependent) products and the corresponding types
-- of (non-dependent) n-ary functions. The representation works well with
-- inference thus allowing us to use generic combinators to manipulate
-- such functions.

open import N-ary

------------------------------------------------------------------------
-- Examples of Arrows n As B
------------------------------------------------------------------------

module _ {a} {A : Set a} where

\end{code}
%<*all>
\begin{code}
  _ : Arrows 2 ((A → Set p) , List A , _) (Set (p ⊔ a))
  _ = All
\end{code}
%</all>
\begin{code}

\end{code}
%<*appw>
\begin{code}
_<⋆>_ : ∀[ Pw (R ⇒ S) ⇒ Pw R ⇒ Pw S ]
\end{code}
%</appw>
\begin{code}
[]        <⋆> []        = []
(f ∷ fs)  <⋆> (x ∷ xs)  = (f x) ∷ (fs <⋆> xs)
\end{code}
