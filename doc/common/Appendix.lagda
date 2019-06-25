\begin{code}

open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.List

\end{code}
%<*congtype>
\begin{code}
cong : ∀ {a b} {A : Set a} {B : Set b} {x y : A} →
       (f : A → B) → x ≡ y → f x ≡ f y
\end{code}
%</congtype>
\begin{code}
cong f refl = refl


\end{code}
%<*map>
\begin{code}
map : ∀ {a b} {A : Set a} {B : Set b} →
      (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs
\end{code}
%</map>
\begin{code}


\end{code}
%<*all>
\begin{code}
data All {a p} {A : Set a} (P : A → Set p) :
         List A → Set (a ⊔ p) where
  []   : All P []
  _∷_  : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)
\end{code}
%</all>
\begin{code}

\end{code}
%<*unittest>
\begin{code}
_ : 2 + 3 ≡ 5
_ = refl
\end{code}
%</unittest>
\begin{code}


\end{code}
%<*identity>
\begin{code}
id : ∀ {l} {A : Set l} → A → A
id x = x
\end{code}
%</identity>
\begin{code}

