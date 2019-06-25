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
    R : A → B → Set r
    S : A → B → Set r
    x y t u : A

------------------------------------------------------------------------
-- Lift

\end{code}
%<*lift>
\begin{code}
record Lift ℓ (A : Set a) : Set (ℓ ⊔ a) where
  constructor lift
  field lower : A
\end{code}
%</lift>
\begin{code}

------------------------------------------------------------------------
-- Constant function

private
  module DISPLAYONLY {a} {i} {I : Set i} where
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

------------------------------------------------------------------------
-- Type annotation

\end{code}
%<*annot>
\begin{code}
_∋_ : ∀ {a} (A : Set a) → A → A
A ∋ a = a
\end{code}
%</annot>
\begin{code}

------------------------------------------------------------------------
-- Empty

\end{code}
%<*bot>
\begin{code}
data ⊥ : Set where
\end{code}
%</bot>
\begin{code}

\end{code}
%<*botelim>
\begin{code}
⊥-elim : ⊥ → A
⊥-elim ()
\end{code}
%</botelim>
\begin{code}

------------------------------------------------------------------------
-- Unit

\end{code}
%<*unit>
\begin{code}
record ⊤ : Set where
  constructor tt
\end{code}
%</unit>
\begin{code}


------------------------------------------------------------------------
-- Product

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

infixr 2 _×_
_×_ : Set a → Set b → Set (a ⊔ b)
A × B = Σ A λ _ → B

curry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : (a : A) → B a → Set c}
        (f : (p : Σ A B) → C (Σ.proj₁ p) (Σ.proj₂ p)) →
        (a : A) (b : B a) → C a b
curry f a b = f (a , b)


uncurry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : (a : A) → B a → Set c}
          (f : (a : A) (b : B a) → C a b) →
          (p : Σ A B) → C (Σ.proj₁ p) (Σ.proj₂ p)
uncurry f (a , b) = f a b

------------------------------------------------------------------------
-- Sum

\end{code}
%<*sum>
\begin{code}
data _⊎_ (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B
\end{code}
%</sum>
\begin{code}

------------------------------------------------------------------------
-- Equality

\end{code}
%<*equality>
\begin{code}
data _≡_ {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x
\end{code}
%</equality>
\begin{code}

-- congruence

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

-- substitution

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

------------------------------------------------------------------------
-- List

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

-- named module to avoid clash with the `map` defined later on
module Listy {a b} {A : Set a} {B : Set b} where

  map : (f : A → B) → List A → List B
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  zipWith : ∀ {c} {C : Set c} → (A → B → C) → List A → List B → List C
  zipWith f (a ∷ as) (b ∷ bs) = f a b ∷ zipWith f as bs
  zipWith f _ _ = []

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

-- All

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

-- Any

\end{code}
%<*any>
\begin{code}
  data Any (P : A → Set p) : List A → Set (a ⊔ p) where
    here   : P x → Any P (x ∷ xs)
    there  : Any P xs → Any P (x ∷ xs)
\end{code}
%</any>
\begin{code}

------------------------------------------------------------------------
-- Working with indexed families
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Quantifiers

-- Universal

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

\end{code}
%<*replicate>
\begin{code}
replicate : ∀[ P ] → Π[ All P ]
replicate p []        = []
replicate p (x ∷ xs)  = p ∷ replicate p xs
\end{code}
%</replicate>
\begin{code}

-- Existential

\end{code}
%<*exists>
\begin{code}
∃⟨_⟩ : {A : Set a} (P : A → Set p) → Set (a ⊔ p)
∃⟨ P ⟩ = Σ _ P
\end{code}
%</exists>
\begin{code}

\end{code}
%<*satisfiable>
\begin{code}
satisfiable : ∃⟨ All P ⟩
satisfiable = [] , []
\end{code}
%</satisfiable>
\begin{code}

\end{code}
%<*toList>
\begin{code}
toList : ∃⟨ All P ⟩ → List ∃⟨ P ⟩
toList ([]      , [])      = []
toList (x ∷ xs  , p ∷ ps)  = (x , p) ∷ toList (xs , ps)
\end{code}
%</toList>
\begin{code}

------------------------------------------------------------------------
-- Lifted type constructors

-- Implication

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
%<*map>
\begin{code}
map : ∀[ P ⇒ Q ] → ∀[ All P ⇒ All Q ]
map f []          = []
map f (px ∷ pxs)  = f px ∷ map f pxs
\end{code}
%</map>
\begin{code}

private
  module ALLAP where
\end{code}
%<*ap>
\begin{code}
    _<⋆>_ : ∀[ All (P ⇒ Q) ⇒ All P ⇒ All Q ]
    []        <⋆> []        = []
    (f ∷ fs)  <⋆> (x ∷ xs)  = f x ∷ (fs <⋆> xs)
\end{code}
%</ap>
\begin{code}

-- Conjunction

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

-- Disjunction

\end{code}
%<*disjunction>
\begin{code}
_∪_ : (I → Set p) → (I → Set q) → (I → Set (p ⊔ q))
(P ∪ Q) i = (P i) ⊎ (Q i)
\end{code}
%</disjunction>
\begin{code}

\end{code}
%<*decide>
\begin{code}
decide : Π[ P ∪ Q ] → Π[ Any P ∪ All Q ]
decide pq? []       = inj₂ []
decide pq? (x ∷ xs) with pq? x | decide pq? xs
... | inj₁ px | _ = inj₁ (here px)
... | _ | inj₁ ap = inj₁ (there ap)
... | inj₂ qx | inj₂ qxs = inj₂ (qx ∷ qxs)
\end{code}
%</decide>
\begin{code}

\end{code}
%<*negation>
\begin{code}
¬_ : (I → Set p) → (I → Set p)
(¬ P) i = P i → ⊥
\end{code}
%</negation>
\begin{code}

\end{code}
%<*anynotall>
\begin{code}
notall : ∀[ Any (¬ P) ⇒ ¬ All P ]
notall (here ¬px) (px ∷ _)  = ⊥-elim (¬px px)
notall (there ¬p) (_ ∷ ps)  = notall ¬p ps
\end{code}
%</anynotall>
\begin{code}

\end{code}
%<*none>
\begin{code}
none : ∀[ ¬ P ] → ∀[ ¬ Any P ]
none ¬p (here px)  = ¬p px
none ¬p (there p)  = none ¬p p
\end{code}
%</none>
\begin{code}

\end{code}
%<*empty>
\begin{code}
empty : ∀[ All (const ⊥) ⇒ (List A ∋ []) ≡_ ]
empty [] = refl
\end{code}
%</empty>
\begin{code}

------------------------------------------------------------------------
-- Changes to the index

\end{code}
%<*update>
\begin{code}
_⊢_ : (I → J) → (J → Set p) → (I → Set p)
(f ⊢ P) i = P (f i)
\end{code}
%</update>
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

------------------------------------------------------------------------
-- Broken: Working with binary relations

module _ {A : Set a} {B : Set b} where
\end{code}
%<*pointwise>
\begin{code}
  data Pw (R : A → B → Set r) :
          List A → List B → Set (a ⊔ b ⊔ r) where
    []   : Pw R [] []
    _∷_  : R x y → Pw R xs ys → Pw R (x ∷ xs) (y ∷ ys)
\end{code}
%</pointwise>
\begin{code}

\end{code}
%<*appw>
\begin{code}
_<⋆>_ : ∀[ Pw (λ x → R x ⇒ S x) xs ⇒
           Pw R xs ⇒ Pw S xs ]
\end{code}
%</appw>
\begin{code}
[]        <⋆> []        = []
(f ∷ fs)  <⋆> (x ∷ xs)  = (f x) ∷ (fs <⋆> xs)
\end{code}
