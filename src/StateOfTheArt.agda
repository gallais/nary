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


record Lift ℓ (A : Set a) : Set (ℓ ⊔ a) where
  constructor lift
  field lower : A


------------------------------------------------------------------------
-- Constant function

private
  module DISPLAYONLY {a} {i} {I : Set i} where

    const : Set a → (I → Set a)
    const A i = A


const : A → (I → A)
const a i = a

------------------------------------------------------------------------
-- Type annotation


_∋_ : ∀ {a} (A : Set a) → A → A
A ∋ a = a


------------------------------------------------------------------------
-- Empty


data ⊥ : Set where



⊥-elim : ⊥ → A
⊥-elim ()


------------------------------------------------------------------------
-- Unit


record ⊤ : Set where
  constructor tt



------------------------------------------------------------------------
-- Product

infixr 8 _,_

record Σ (A : Set a) (P : A → Set p) : Set (a ⊔ p) where
  constructor _,_
  field proj₁ : A
        proj₂ : P proj₁


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


data _⊎_ (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B


------------------------------------------------------------------------
-- Equality


data _≡_ {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x


-- congruence


cong : (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl



cong₂ :  (f : A → B → C) →
         x ≡ y → t ≡ u → f x t ≡ f y u
cong₂ f refl refl = refl


-- substitution


subst : (P : A → Set p) → x ≡ y → P x → P y
subst P refl px = px



subst₂ :  (R : A → B → Set p) →
          x ≡ y → t ≡ u → R x t → R y u
subst₂ P refl refl pr = pr


------------------------------------------------------------------------
-- List

infixr 9 _∷_

data List (A : Set a) : Set a where
  []   : List A
  _∷_  : A → List A → List A


-- named module to avoid clash with the `map` defined later on
module Listy {a b} {A : Set a} {B : Set b} where

  map : (f : A → B) → List A → List B
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  zipWith : ∀ {c} {C : Set c} → (A → B → C) → List A → List B → List C
  zipWith f (a ∷ as) (b ∷ bs) = f a b ∷ zipWith f as bs
  zipWith f _ _ = []


concat : List (List A) → List A
concat []                 = []
concat ([]        ∷ xss)  = concat xss
concat ((x ∷ xs)  ∷ xss)  = x ∷ concat (xs ∷ xss)


-- All

private
  variable
    xs ys : List A

module _ {A : Set a} where


  data All (P : A → Set p) : List A → Set (a ⊔ p) where
    []   : All P []
    _∷_  : P x → All P xs → All P (x ∷ xs)


-- Any


  data Any (P : A → Set p) : List A → Set (a ⊔ p) where
    here   : P x → Any P (x ∷ xs)
    there  : Any P xs → Any P (x ∷ xs)


------------------------------------------------------------------------
-- Working with indexed families
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Quantifiers

-- Universal


module _ {I : Set i} where

  ∀[_] : (I → Set p) → Set (i ⊔ p)
  ∀[ P ] = ∀ {i} → P i


module _ {I : Set i} where

  Π[_] : (I → Set p) → Set (i ⊔ p)
  Π[ P ] = ∀ i → P i



replicate : ∀[ P ] → Π[ All P ]
replicate p []        = []
replicate p (x ∷ xs)  = p ∷ replicate p xs


-- Existential


∃⟨_⟩ : {A : Set a} (P : A → Set p) → Set (a ⊔ p)
∃⟨ P ⟩ = Σ _ P



satisfiable : ∃⟨ All P ⟩
satisfiable = [] , []



toList : ∃⟨ All P ⟩ → List ∃⟨ P ⟩
toList ([]      , [])      = []
toList (x ∷ xs  , p ∷ ps)  = (x , p) ∷ toList (xs , ps)


------------------------------------------------------------------------
-- Lifted type constructors

-- Implication

infixr 9 _⇒_

_⇒_ : (I → Set p) → (I → Set q) → (I → Set (p ⊔ q))
(P ⇒ Q) i = P i → Q i



map : ∀[ P ⇒ Q ] → ∀[ All P ⇒ All Q ]
map f []          = []
map f (px ∷ pxs)  = f px ∷ map f pxs


private
  module ALLAP where

    _<⋆>_ : ∀[ All (P ⇒ Q) ⇒ All P ⇒ All Q ]
    []        <⋆> []        = []
    (f ∷ fs)  <⋆> (x ∷ xs)  = f x ∷ (fs <⋆> xs)


-- Conjunction


_∩_ : (I → Set p) → (I → Set q) → (I → Set (p ⊔ q))
(P ∩ Q) i = Σ (P i) λ _ → Q i



unzip : ∀[ All (P ∩ Q) ⇒ All P ∩ All Q ]
unzip []               = [] , []
unzip ((p , q) ∷ pqs)  =  let (ps , qs) = unzip pqs
                          in (p ∷ ps) , (q ∷ qs)


-- Disjunction


_∪_ : (I → Set p) → (I → Set q) → (I → Set (p ⊔ q))
(P ∪ Q) i = (P i) ⊎ (Q i)



decide : Π[ P ∪ Q ] → Π[ Any P ∪ All Q ]
decide pq? []       = inj₂ []
decide pq? (x ∷ xs) with pq? x | decide pq? xs
... | inj₁ px | _ = inj₁ (here px)
... | _ | inj₁ ap = inj₁ (there ap)
... | inj₂ qx | inj₂ qxs = inj₂ (qx ∷ qxs)



¬_ : (I → Set p) → (I → Set p)
(¬ P) i = P i → ⊥



notall : ∀[ Any (¬ P) ⇒ ¬ All P ]
notall (here ¬px) (px ∷ _)  = ⊥-elim (¬px px)
notall (there ¬p) (_ ∷ ps)  = notall ¬p ps



none : ∀[ ¬ P ] → ∀[ ¬ Any P ]
none ¬p (here px)  = ¬p px
none ¬p (there p)  = none ¬p p



empty : ∀[ All (const ⊥) ⇒ (List A ∋ []) ≡_ ]
empty [] = refl


------------------------------------------------------------------------
-- Changes to the index


_⊢_ : (I → J) → (J → Set p) → (I → Set p)
(f ⊢ P) i = P (f i)



concat⁺ : ∀[ All (All P) ⇒ concat ⊢ All P ]
concat⁺ []                    = []
concat⁺ ([]          ∷ pxss)  = concat⁺ pxss
concat⁺ ((px ∷ pxs)  ∷ pxss)  = px ∷ concat⁺ (pxs ∷ pxss)


------------------------------------------------------------------------
-- Broken: Working with binary relations

module _ {A : Set a} {B : Set b} where

  data Pw (R : A → B → Set r) :
          List A → List B → Set (a ⊔ b ⊔ r) where
    []   : Pw R [] []
    _∷_  : R x y → Pw R xs ys → Pw R (x ∷ xs) (y ∷ ys)



_<⋆>_ : ∀[ Pw (λ x → R x ⇒ S x) xs ⇒
           Pw R xs ⇒ Pw S xs ]

[]        <⋆> []        = []
(f ∷ fs)  <⋆> (x ∷ xs)  = (f x) ∷ (fs <⋆> xs)
