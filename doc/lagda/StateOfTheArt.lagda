\begin{code}
{-# OPTIONS --safe --without-K #-}

open import Level using (Level; _⊔_)

private
  variable
    a b c p q r i j : Level
    A : Set a
    B : Set b
    C : Set c
    I : Set i
    J : Set j
    P : A → Set p
    Q : A → Set q
    R : A → Set r
    x y t u : A

module _ {A : Set a} where
\end{code}
%<*equality>
\begin{code}
  data _≡_ (x : A) : A → Set a where
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
subst₂ :  (R : A → B → Set p) →
          x ≡ y → t ≡ u → R x t → R y u
subst₂ P refl refl pr = pr
\end{code}
%</subst2>
\begin{code}

infixr 9 _∷_
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

module _ {I : Set i} where
\end{code}
%<*universal>
\begin{code}
  Π[_] : (I → Set p) → Set (i ⊔ p)
  Π[ P ] = ∀ i → P i
\end{code}
%</universal>
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

infixr 8 _,_
\end{code}
%<*sigma>
\begin{code}
record Σ (A : Set a) (P : A → Set p) : Set (a ⊔ p) where
  constructor _,_
  field proj₁ : A
        proj₂ : P proj₁
\end{code}
%</sigma>
\begin{code}

\end{code}
%<*exists>
\begin{code}
∃⟨_⟩ : {A : Set a} (P : A → Set p) → Set (a ⊔ p)
∃⟨ P ⟩ = Σ _ P
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


\end{code}
%<*conjunction>
\begin{code}
_∩_ : (I → Set p) → (I → Set q) → (I → Set (p ⊔ q))
(P ∩ Q) i = Σ (P i) λ _ → Q i
\end{code}
%</conjunction>
\begin{code}

\end{code}
%<*unzip>
\begin{code}
unzip : ∀[ All (P ∩ Q) ⇒ All P ∩ All Q ]
unzip []               = [] , []
unzip ((p , q) ∷ pqs)  =  let (ps , qs) = unzip pqs
                          in (p ∷ ps) , (q ∷ qs)
\end{code}
%</unzip>
\begin{code}

\end{code}
%<*negation>
\begin{code}
data ⊥ : Set where

⊥-elim : ⊥ → A
⊥-elim ()

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
%<*distrib>
\begin{code}
distrib : ∀[ ¬ (_≡ []) ⇒ All (¬ P) ⇒ ¬ All P ]
distrib ne []        []       = ne refl
distrib ne (¬p ∷ _)  (p ∷ _)  = ¬p p
\end{code}
%</distrib>
\begin{code}

\end{code}
%<*empty>
\begin{code}
empty : ∀[ ¬ P ] → ∀[ All P ⇒ [] ≡_ ]
empty ¬p []          = refl
empty ¬p (px ∷ pxs)  = ⊥-elim (¬p px)
\end{code}
%</empty>
\begin{code}

\end{code}
%<*pure>
\begin{code}
pure : ∀[ P ⇒ ¬ ¬ P ]
pure p ¬p = ¬p p
\end{code}
%</pure>
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

private
  module DISPLAYONLY where
\end{code}
%<*const>
\begin{code}
    const : Set a → (I → Set a)
    const A i = A
\end{code}
%</const>
\begin{code}

const : A → (I → A)
const a i = a

\end{code}
%<*toList>
\begin{code}
toList : ∀[ All P ⇒ const (List ∃⟨ P ⟩) ]
toList []          = []
toList (px ∷ pxs)  = (_ , px) ∷ toList pxs
\end{code}
%</toList>
\begin{code}


\end{code}
%<*update>
\begin{code}
_⊢_ : (I → J) → (J → Set p) → (I → Set p)
(f ⊢ P) i = P (f i)
\end{code}
%</update>
\begin{code}


\end{code}
%<*concat>
\begin{code}
concat : List (List A) → List A
concat []                 = []
concat ([]        ∷ xss)  = concat xss
concat ((x ∷ xs)  ∷ xss)  = x ∷ concat (xs ∷ xss)
\end{code}
%</concat>
\begin{code}


\end{code}
%<*join>
\begin{code}
concat⁺ : ∀[ All (All P) ⇒ concat ⊢ All P ]
concat⁺ []                    = []
concat⁺ ([]          ∷ pxss)  = concat⁺ pxss
concat⁺ ((px ∷ pxs)  ∷ pxss)  = px ∷ concat⁺ (pxs ∷ pxss)
\end{code}
%</join>
\begin{code}

open import Agda.Builtin.Nat
  using (zero; suc)
  renaming (Nat to ℕ)
  public

\end{code}
%<*lesseq>
\begin{code}
data _≤_ : (m n : ℕ) → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n
\end{code}
%</lesseq>
\begin{code}

_<_ : (m n : ℕ) → Set
m < n = suc m ≤ n

_>_ : (m n : ℕ) → Set
m > n = n < m

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
