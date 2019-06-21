\begin{code}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality


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

