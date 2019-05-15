\begin{code}
module Printf where

open import Level using (0ℓ)
open import StateOfTheArt
  using ( ℕ; zero; suc
        ; Σ; _,_
        )
open import N-ary
open import Function
open import Data.List.Base using (List; []; _∷_)
open import Data.String using (String; concat)
open import Data.Nat.Show

\end{code}
%<*chunk>
\begin{code}
data Chunk : Set where
  Nat  : Chunk
  Raw  : String → Chunk
\end{code}
%</chunk>
\begin{code}


Format = List Chunk

size : Format → ℕ
size []             = zero
size (Nat    ∷ f)  = suc (size f)
size (Raw _  ∷ f)  = size f

0ℓs : ∀ {n} → Levels n
0ℓs {zero}  = _
0ℓs {suc n} = 0ℓ , 0ℓs

\end{code}
%<*format>
\begin{code}
format : (f : Format) → Sets (size f) 0ℓs
format []            = _
format (Nat    ∷ f)  = ℕ , format f
format (Raw _  ∷ f)  = format f
\end{code}
%</format>
\begin{code}

\end{code}
%<*assemble>
\begin{code}
assemble : ∀ f → Product _ (format f) → List String
assemble []            vs        = []
assemble (Nat    ∷ f)  (n , vs)  = show n ∷ assemble f vs
assemble (Raw s  ∷ f)  vs        = s ∷ assemble f vs
\end{code}
%</assemble>
\begin{code}

\end{code}
%<*printf>
\begin{code}
printf : ∀ f → Arrows _ (format f) String
printf f = curry (size f) (concat ∘ assemble f)
\end{code}
%</printf>
\begin{code}

\end{code}
%<*example>
\begin{code}
_ : ℕ → ℕ → String
_ = printf (Nat ∷ Raw " < " ∷ Nat ∷ [])
\end{code}
%</example>
\begin{code}



\end{code}
