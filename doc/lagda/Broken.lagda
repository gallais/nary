\begin{code}
module Broken where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base
open import Relation.Binary.PropositionalEquality

\end{code}
%<*function>
\begin{code}
record Function : Set₁ where
  constructor _⇉_
  field  domains   : List Set
         codomain  : Set
\end{code}
%</function>
\begin{code}

\end{code}
%<*sem>
\begin{code}
⟦_⟧ : Function → Set
⟦ As ⇉ B ⟧ = foldr (λ A B → A → B) B As
\end{code}
%</sem>
\begin{code}

\end{code}
%<*plus>
\begin{code}
_+_ : ⟦ (ℕ ∷ ℕ ∷ []) ⇉ ℕ ⟧
\end{code}
%</plus>
\begin{code}
zero   + n = n
suc m  + n = suc (m + n)
\end{code}

\end{code}
%<*conflict1>
\begin{code}
_ : ⟦ (ℕ ∷ []) ⇉ ℕ ⟧ ≡ (ℕ → ℕ)
_ = refl
\end{code}
%</conflict1>
\begin{code}

\end{code}
%<*conflict2>
\begin{code}
_ : ⟦ [] ⇉ (ℕ → ℕ) ⟧ ≡ (ℕ → ℕ)
_ = refl
\end{code}
%</conflict2>
\begin{code}
