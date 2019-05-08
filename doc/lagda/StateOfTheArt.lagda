\begin{code}
{-# OPTIONS --safe --without-K #-}

open import Data.Empty
open import Level using (Level; _⊔_)

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
    x y t u : A

\end{code}
%<*equality>
\begin{code}
data _≡_ {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x
\end{code}
%</equality>
\begin{code}


\end{code}
%<*cong>
\begin{code}
cong : (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl
\end{code}
%</cong>
\begin{code}

\end{code}
%<*cong2>
\begin{code}
cong₂ :  (f : A → B → C) →
         x ≡ y → t ≡ u → f x t ≡ f y u
cong₂ f refl refl = refl
\end{code}
%</cong2>
\begin{code}


\end{code}
%<*subst>
\begin{code}
subst : (P : A → Set p) → x ≡ y → P x → P y
subst P refl px = px
\end{code}
%</subst>
\begin{code}

\end{code}
%<*subst2>
\begin{code}
subst₂ :  (P : A → B → Set p) →
          x ≡ y → t ≡ u → P x t → P y u
subst₂ P refl refl pxt = pxt
\end{code}
%</subst2>
\begin{code}


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

\end{code}
%<*nat>
\begin{code}
data ℕ : Set where
  zero  : ℕ
  suc   : ℕ → ℕ
\end{code}
%</nat>
\begin{code}

\end{code}
%<*lesseq>
\begin{code}
data _≤_ : (m n : ℕ) → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n
\end{code}
%</lesseq>
\begin{code}


\end{code}
%<*greateq>
\begin{code}
_≥_ : (m n : ℕ) → Set
m ≥ n = n ≤ m
\end{code}
%</greateq>
\begin{code}

private
  variable
    m n : ℕ

\end{code}
%<*brokenantisym>
\begin{code}
antisym : ∀[ (m ≥_) ⇒ (m ≤_) ⇒ (m ≡_) ]
\end{code}
%</brokenantisym>
\begin{code}
antisym z≤n        z≤n        = refl
antisym (s≤s m≥n)  (s≤s m≤n)  = cong suc (antisym m≥n m≤n)


\end{code}
