\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}

module Unifier where

open import N-ary
  using (_×_; ⊤)
open import StateOfTheArt
  using ( ℕ; zero; suc; _+_
        ; _,_
        ; _≡_; refl
        )

\end{code}
%<*unifproblem>
\begin{code}
_ : (_ → _) ≡ (ℕ → ℕ)
_ = refl
\end{code}
%</unifproblem>
\begin{code}


\end{code}
%<*unifconstr>
\begin{code}
_ : (ℕ → _) ≡ (ℕ → ℕ)
_ = refl
\end{code}
%</unifconstr>
\begin{code}

\end{code}
%<*instantiation>
\begin{code}
_ : _ ≡ (_ → _)
_ = refl
\end{code}
%</instantiation>
\begin{code}

private
  variable
    A : Set

\end{code}
%<*nary>
\begin{code}
nary : ℕ → Set → Set
nary zero     A = A
nary (suc n)  A = ℕ → nary n A
\end{code}
%</nary>
\begin{code}

\end{code}
%<*at0>
\begin{code}
at0 : ∀ n → nary n A → A
at0 zero    f = f
at0 (suc n) f = at0 n (f 0)
\end{code}
%</at0>
\begin{code}


\end{code}
%<*normalised1>
\begin{code}
_ : nary 1 _ ≡ (ℕ → ℕ)
_ = refl
\end{code}
%</normalised1>
\begin{code}

\end{code}
%<*normalised0>
\begin{code}
_ : nary 0 _ ≡ (ℕ → ℕ)
_ = refl
\end{code}
%</normalised0>
\begin{code}

\end{code}
%<*unsolved>
\begin{code}
_ : nary _ _ ≡ (ℕ → ℕ)
_ = refl
\end{code}
%</unsolved>
\begin{code}

\end{code}
%<*inverted0>
\begin{code}
_ : nary _ ℕ ≡ ℕ
_ = refl
\end{code}
%</inverted0>

\end{code}
%<*inverted>
\begin{code}
_ : nary _ ℕ ≡ (ℕ → ℕ)
_ = refl
\end{code}
%</inverted>


\end{code}
%<*notinverted>
\begin{code}
_ : nary _ (ℕ → ℕ) ≡ (ℕ → ℕ)
_ = refl
\end{code}
%</notinverted>
