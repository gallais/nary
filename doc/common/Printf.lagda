\begin{code}
module Printf where

open import Level using (0ℓ)
open import StateOfTheArt
  using ( Σ; _,_
        ; _≡_; refl
        )
open import N-ary
open import Function
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
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

\end{code}
%<*chunks>
\begin{code}
Format : Set
Format = List Chunk
\end{code}
%</chunks>
\begin{code}


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
format : (fmt : Format) → Sets (size fmt) 0ℓs
format []            = _
format (Nat    ∷ f)  = ℕ , format f
format (Raw _  ∷ f)  = format f
\end{code}
%</format>
\begin{code}

\end{code}
%<*assemble>
\begin{code}
assemble : ∀ fmt → Product _ (format fmt) → List String
assemble []              vs        = []
assemble (Nat    ∷ fmt)  (n , vs)  = show n ∷ assemble fmt vs
assemble (Raw s  ∷ fmt)  vs        = s ∷ assemble fmt vs
\end{code}
%</assemble>
\begin{code}

\end{code}
%<*printf>
\begin{code}
printf : ∀ fmt → Arrows _ (format fmt) String
printf fmt = curryₙ (size fmt) (concat ∘ assemble fmt)
\end{code}
%</printf>
\begin{code}

\end{code}
%<*example>
\begin{code}
lessThan : ℕ → ℕ → String
lessThan = printf (Nat ∷ Raw " < " ∷ Nat ∷ [])
\end{code}
%</example>
\begin{code}

\end{code}
%<*test>
\begin{code}
_ : lessThan 2 5 ≡ "2 < 5"
_ = refl
\end{code}
%</test>
\begin{code}

\end{code}
