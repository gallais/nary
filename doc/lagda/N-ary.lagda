\begin{code}
{-# OPTIONS --without-K --safe #-}

module N-ary where

open import Level as L using (Level; 0ℓ; _⊔_)
open import StateOfTheArt as Unary
  hiding ( ∃⟨_⟩; ∀[_]; Π[_]; _⇒_; _∩_; _∪_; ¬_
         ; _≡_; refl; ⊥
         ; map
         )
open import Relation.Binary.PropositionalEquality
open import Data.Empty
-- open import Data.Fin.Base using (Fin; zero; suc)
open import Function using (_∘_)

private
  variable
    a b c r s : Level
    A : Set a
    B : Set b
    C : Set c
    R : Set r

------------------------------------------------------------------------
-- Building blocks of right-nested product

\end{code}
%<*unit>
\begin{code}
record ⊤ : Set where
  constructor tt
\end{code}
%</unit>
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
-- Concrete examples can be found in README.N-ary. This file's comments
-- are more focused on the implementation details and the motivations
-- behind the design decisions.

------------------------------------------------------------------------
-- Type Definitions

-- We want to define n-ary products and generic n-ary operations on them
-- such as currying and uncurrying. We want users to be able to use these
-- seamlessly whenever n is concrete. In other words, we want Agda to infer
-- the sets `A₁, ⋯, Aₙ` when we write `uncurryₙ n f` where `f` has type
-- `A₁ → ⋯ → Aₙ → B`. For this to happen, we need the structure in which
-- these Sets are stored to effectively η-expand to `A₁, ⋯, Aₙ` when the
-- parameter `n` is known.

-- Hence the following definitions:
------------------------------------------------------------------------

-- First, a "vector" of `n` Levels (defined by induction on n so that it
-- may be built by η-expansion and unification). Each Level will be that
-- of one of the Sets we want to take the n-ary product of.

\end{code}
%<*levels>
\begin{code}
Levels : ℕ → Set
Levels zero     = ⊤
Levels (suc n)  = Level × Levels n
\end{code}
%</levels>
\begin{code}


private
  variable
    n : ℕ
    ls : Levels n

-- The overall product's Level will be the least upper bound of all of the
-- Levels involved.

\end{code}
%<*tolevel>
\begin{code}
⨆ : ∀ n → Levels n → Level
⨆ zero     _         = 0ℓ
⨆ (suc n)  (l , ls)  = l ⊔ (⨆ n ls)
\end{code}
%</tolevel>
\begin{code}

-- Second, a "vector" of `n` Sets whose respective Levels are determined
-- by the `Levels n` input.


\end{code}
%<*sets>
\begin{code}
Sets : ∀ n (ls : Levels n) → Set (L.suc (⨆ n ls))
Sets zero     _         = Lift _ ⊤
Sets (suc n)  (l , ls)  = Set l × Sets n ls
\end{code}
%</sets>
\begin{code}

\end{code}
%<*smap>
\begin{code}
_<$>_ : (∀ {l} → Set l → Set l) →
        ∀ {n ls} → Sets n ls → Sets n ls
_<$>_ f {zero}   as        = _
_<$>_ f {suc n}  (a , as)  = f a , f <$> as
\end{code}
%</smap>
\begin{code}

private
  variable
    as : Sets n ls

-- Third, the n-ary product itself: provided n Levels and a corresponding
-- "vector" of `n` Sets, we can build a big right-nested product type packing
-- a value for each one of these Sets. We have a special case for 1 because
-- we want our `(un)curryₙ` functions to work for user-written functions and
-- they rarely are ⊤-terminated.

\end{code}
%<*product>
\begin{code}
Product : ∀ n {ls} → Sets n ls → Set (⨆ n ls)
Product zero     _         = ⊤
Product (suc n)  (a , as)  = a × Product n as
\end{code}
%</product>
\begin{code}

-- Similarly we may want to talk about a function whose domains are given
-- by a "vector" of `n` Sets and whose codomain is B. `Arrows` forms such
-- a type of shape `A₁ → ⋯ → Aₙ → B` by induction on `n`.


\end{code}
%<*arrows>
\begin{code}
Arrows : ∀ n {ls} → Sets n ls → Set r → Set (r ⊔ (⨆ n ls))
Arrows zero     _         b = b
Arrows (suc n)  (a , as)  b = a → Arrows n as b
\end{code}
%</arrows>
\begin{code}


------------------------------------------------------------------------
-- Generic Programs

-- Once we have these type definitions, we can write generic programs
-- over them. They will typically be split into two or three definitions:

-- 1. action on the vector of n levels (if any)
-- 2. action on the corresponding vector of n Sets
-- 3. actual program, typed thank to the function defined in step 2.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- n-ary versions of `cong` and `subst`

\end{code}
%<*Cong>
\begin{code}
Congₙ : ∀ n {ls} {as : Sets n ls} {R : Set r} →
        (f g : Arrows n as R) → Set (r ⊔ (⨆ n ls))
Congₙ zero     f g = f ≡ g
Congₙ (suc n)  f g = ∀ {x y} → x ≡ y → Congₙ n (f x) (g y)
\end{code}
%</Cong>
\begin{code}

\end{code}
%<*cong>
\begin{code}
congₙ : ∀ n {ls} {as : Sets n ls} {R : Set r} →
        (f : Arrows n as R) → Congₙ n f f
congₙ zero     f       = refl
congₙ (suc n)  f refl  = congₙ n (f _)
\end{code}
%</cong>
\begin{code}

\end{code}
%<*Subst>
\begin{code}
Substₙ : ∀ n {ls} {as : Sets n ls} →
         (f g : Arrows n as (Set r)) → Set (r ⊔ (⨆ n ls))
Substₙ zero     f g = f → g
Substₙ (suc n)  f g = ∀ {x y} → x ≡ y → Substₙ n (f x) (g y)
\end{code}
%</Subst>
\begin{code}

\end{code}
%<*subst>
\begin{code}
substₙ : ∀ {n r ls} {as : Sets n ls} →
         (f : Arrows n as (Set r)) → Substₙ n f f
substₙ {zero}   f x     = x
substₙ {suc n}  f refl  = substₙ (f _)
\end{code}
%</subst>
\begin{code}

------------------------------------------------------------------------
-- (un)curry

-- We start by defining `curryₙ` and `uncurryₙ` converting back and forth
-- between `A₁ → ⋯ → Aₙ → B` and `(A₁ × ⋯ × Aₙ) → B` by induction on `n`.

\end{code}
%<*curry>
\begin{code}
curryₙ : ∀ n {ls} {as : Sets n ls} →
         (Product n as → R) → Arrows n as R
curryₙ zero     f = f _
curryₙ (suc n)  f = curryₙ n ∘ curry f
\end{code}
%</curry>
\begin{code}

\end{code}
%<*uncurry>
\begin{code}
uncurryₙ : ∀ n {ls} {as : Sets n ls} →
           Arrows n as R → (Product n as → R)
uncurryₙ zero     f = const f
uncurryₙ (suc n)  f = uncurry (uncurryₙ n ∘ f)
\end{code}
%</uncurry>
\begin{code}


module _ {a b} {A : Set a} {B : Set b} where

  map : (f : A → B) → List A → List B
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  zipWith : ∀ {c} {C : Set c} → (A → B → C) → List A → List B → List C
  zipWith f (a ∷ as) (b ∷ bs) = f a b ∷ zipWith f as bs
  zipWith f _ _ = []

open import Function using (_∘_; flip; _$_)

\end{code}
%<*zw-aux-type>
\begin{code}
zw-aux : ∀ n {ls} {as : Sets n ls} →
         (Product n as → R) →
         (Product n (List <$> as) → List R)
\end{code}
%</zw-aux-type>
%<*zw-aux0>
\begin{code}
zw-aux 0 f as = []
\end{code}
%</zw-aux0>
%<*zw-aux1>
\begin{code}
zw-aux 1 f (as , _) = map (f ∘ (_, tt)) as
\end{code}
%</zw-aux1>
%<*zw-auxn>
\begin{code}
zw-aux (suc n) f (as , ass) = zipWith _$_ fs as
  where fs = zw-aux n (flip (curry f)) ass
\end{code}
%</zw-auxn>
\begin{code}


\end{code}
%<*zipWith>
\begin{code}
zipWithₙ : ∀ n {ls} {as : Sets n ls} →
           Arrows n as R → Arrows n (List <$> as) (List R)
zipWithₙ n f = curryₙ n (zw-aux n (uncurryₙ n f))
\end{code}
%</zipWith>
\begin{code}


------------------------------------------------------------------------
-- projection of the k-th component

-- To know at which Set level the k-th projection out of an n-ary product
-- lives, we need to extract said level, by induction on k.
{-

Levelₙ : ∀ {n} → Levels n → Fin n → Level
Levelₙ (l , _)  zero    = l
Levelₙ (_ , ls) (suc k) = Levelₙ ls k

-- Once we have the Sets used in the product, we can extract the one we
-- are interested in, once more by induction on k.

Projₙ : ∀ {n ls} → Sets n ls → ∀ k → Set (Levelₙ ls k)
Projₙ (a , _)  zero    = a
Projₙ (_ , as) (suc k) = Projₙ as k

-- Finally, provided a Product of these sets, we can extract the k-th value.
-- `projₙ` takes both `n` and `k` explicitly because we expect the user will
-- be using a concrete `k` (potentially manufactured using `Data.Fin`'s `#_`)
-- and it will not be possible to infer `n` from it.

projₙ : ∀ n {ls} {as : Sets n ls} k → Product n as → Projₙ as k
projₙ 1               zero    v        = v
projₙ (suc n@(suc _)) zero    (v , _)  = v
projₙ (suc n@(suc _)) (suc k) (_ , vs) = projₙ n k vs
projₙ 1 (suc ()) v
-}
------------------------------------------------------------------------
-- removal of the k-th component

{-
Levelₙ⁻ : ∀ {n} → Levels n → Fin n → Levels (pred n)
Levelₙ⁻               (_ , ls) zero    = ls
Levelₙ⁻ {suc (suc _)} (l , ls) (suc k) = l , Levelₙ⁻ ls k
Levelₙ⁻ {1} _ (suc ())

Removeₙ : ∀ {n ls} → Sets n ls → ∀ k → Sets (pred n) (Levelₙ⁻ ls k)
Removeₙ               (_ , as) zero    = as
Removeₙ {suc (suc _)} (a , as) (suc k) = a , Removeₙ as k
Removeₙ {1} _ (suc ())

removeₙ : ∀ n {ls} {as : Sets n ls} k →
          Product n as → Product (pred n) (Removeₙ as k)
removeₙ (suc zero)          zero    _        = _
removeₙ (suc (suc _))       zero    (_ , vs) = vs
removeₙ (suc (suc zero))    (suc k) (v , _)  = v
removeₙ (suc (suc (suc _))) (suc k) (v , vs) = v , removeₙ _ k vs
removeₙ (suc zero) (suc ()) _
-}
------------------------------------------------------------------------
-- insertion of a k-th component
{-
Levelₙ⁺ : ∀ {n} → Levels n → Fin (suc n) → Level → Levels (suc n)
Levelₙ⁺         ls       zero    l⁺ = l⁺ , ls
Levelₙ⁺ {suc _} (l , ls) (suc k) l⁺ = l , Levelₙ⁺ ls k l⁺
Levelₙ⁺ {0} _ (suc ())

Insertₙ : ∀ {n ls l⁺} → Sets n ls → ∀ k (a⁺ : Set l⁺) → Sets (suc n) (Levelₙ⁺ ls k l⁺)
Insertₙ         as       zero    a⁺ = a⁺ , as
Insertₙ {suc _} (a , as) (suc k) a⁺ = a , Insertₙ as k a⁺
Insertₙ {zero} _ (suc ()) _

insertₙ : ∀ n {ls l⁺} {as : Sets n ls} {a⁺ : Set l⁺} k (v⁺ : a⁺) →
          Product n as → Product (suc n) (Insertₙ as k a⁺)
insertₙ 0             zero    v⁺ vs       = v⁺
insertₙ (suc n)       zero    v⁺ vs       = v⁺ , vs
insertₙ 1             (suc k) v⁺ vs       = vs , insertₙ 0 k v⁺ _
insertₙ (suc (suc n)) (suc k) v⁺ (v , vs) = v , insertₙ _ k v⁺ vs
insertₙ 0 (suc ()) _ _
-}
------------------------------------------------------------------------
-- update of a k-th component
{-
Levelₙᵘ : ∀ {n} → Levels n → Fin n → Level → Levels n
Levelₙᵘ (_ , ls) zero    lᵘ = lᵘ , ls
Levelₙᵘ (l , ls) (suc k) lᵘ = l , Levelₙᵘ ls k lᵘ

Updateₙ : ∀ {n ls lᵘ} (as : Sets n ls) k (aᵘ : Set lᵘ) → Sets n (Levelₙᵘ ls k lᵘ)
Updateₙ (_ , as) zero    aᵘ = aᵘ , as
Updateₙ (a , as) (suc k) aᵘ = a , Updateₙ as k aᵘ

updateₙ : ∀ n {ls lᵘ} {as : Sets n ls} k {aᵘ : _ → Set lᵘ} (f : ∀ v → aᵘ v)
          (vs : Product n as) → Product n (Updateₙ as k (aᵘ (projₙ n k vs)))
updateₙ 1             zero    f v        = f v
updateₙ (suc (suc _)) zero    f (v , vs) = f v , vs
updateₙ (suc (suc _)) (suc k) f (v , vs) = v , updateₙ _ k f vs
updateₙ 1 (suc ()) _ _

updateₙ′ : ∀ n {ls lᵘ} {as : Sets n ls} k {aᵘ : Set lᵘ} (f : Projₙ as k → aᵘ) →
           Product n as → Product n (Updateₙ as k aᵘ)
updateₙ′ n k = updateₙ n k
-}
------------------------------------------------------------------------
-- compose function at the n-th position

{-
composeₙ : ∀ n {ls r} {as : Sets n ls} {b : Set r} →
           ∀ {lᵒ lⁿ} {aᵒ : Set lᵒ} {aⁿ : Set lⁿ} →
           (aⁿ → aᵒ) → Arrows n as (aᵒ → b) → Arrows n as (aⁿ → b)
composeₙ zero    f g = g ∘ f
composeₙ (suc n) f g = composeₙ n f ∘ g
-}
------------------------------------------------------------------------
-- mapping under n arguments

open import Function using (_∘_)

mapₙ : ∀ n {ls r s} {as : Sets n ls} {b : Set r} {c : Set s} →
       (b → c) → Arrows n as b → Arrows n as c
mapₙ zero    f v = f v
mapₙ (suc n) f g = mapₙ n f ∘ g

------------------------------------------------------------------------
-- hole at the n-th position

holeₙ : ∀ n {ls r lʰ} {as : Sets n ls} {b : Set r} {aʰ : Set lʰ} →
        (aʰ → Arrows n as b) → Arrows n as (aʰ → b)
holeₙ zero    f = f
holeₙ (suc n) f = holeₙ n ∘ flip f

------------------------------------------------------------------------
-- function constant in its n first arguments

-- Note that its type will only be inferred if it is used in a context
-- specifying what the type of the function ought to be. Just like the
-- usual const: there is no way to infer its domain from its argument.

constₙ : ∀ n {ls r} {as : Sets n ls} {b : Set r} → b → Arrows n as b
constₙ zero    v = v
constₙ (suc n) v = const (constₙ n v)


------------------------------------------------------------------------
-- Generic type constructors

-- `Relation.Unary` provides users with a wealth of combinators to work
-- with indexed sets. We can generalise these to n-ary relations.

-- The crucial thing to notice here is that because we are explicitly
-- considering that the input function should be a `Set`-ended `Arrows`,
-- all the other parameters are inferrable. This allows us to make the
-- number arguments (`n`) implicit.
------------------------------------------------------------------------

infix 5 ∃⟨_⟩ ∀[_] Π[_]

------------------------------------------------------------------------
-- n-ary existential quantifier

\end{code}
%<*quantify>
\begin{code}
quantₙ : (∀ {i l} {I : Set i} → (I → Set l) → Set (i ⊔ l)) →
         ∀ n {ls} {as : Sets n ls} →
         Arrows n as (Set r) → Set (r ⊔ (⨆ n ls))
quantₙ Q zero     f = f
quantₙ Q (suc n)  f = Q (λ x → quantₙ Q n (f x))
\end{code}
%</quantify>
\begin{code}


\end{code}
%<*ex>
\begin{code}
∃⟨_⟩ : Arrows n {ls} as (Set r) → Set (r ⊔ (⨆ n ls))
∃⟨_⟩ = quantₙ Unary.∃⟨_⟩ _
\end{code}
%</ex>
\begin{code}

------------------------------------------------------------------------
-- n-ary universal quantifier

-- implicit

\end{code}
%<*iall>
\begin{code}
∀[_] : Arrows n {ls} as (Set r) → Set (r ⊔ (⨆ n ls))
∀[_] = quantₙ Unary.∀[_] _
\end{code}
%</iall>
\begin{code}

-- explicit

\end{code}
%<*all>
\begin{code}
Π[_] : Arrows n {ls} as (Set r) → Set (r ⊔ (⨆ n ls))
Π[_] = quantₙ Unary.Π[_] _
\end{code}
%</all>
\begin{code}

------------------------------------------------------------------------
-- n-ary pointwise liftings

\end{code}
%<*lift2>
\begin{code}
lift₂ : ∀ n {ls} {as : Sets n ls} → (A → B → C) →
        Arrows n as A → Arrows n as B → Arrows n as C
lift₂ zero     op f g = op f g
lift₂ (suc n)  op f g = λ x → lift₂ n op (f x) (g x)
\end{code}
%</lift2>
\begin{code}

lmap : (Level → Level) → ∀ n → Levels n → Levels n
lmap f zero    ls       = _
lmap f (suc n) (l , ls) = f l , lmap f n ls

smap : ∀ f → (∀ {l} → Set l → Set (f l)) →
       ∀ n {ls} → Sets n ls → Sets n (lmap f n ls)
smap f F zero    as       = _
smap f F (suc n) (a , as) = F a , smap f F n as

palg : ∀ f (F : ∀ {l} → Set l → Set (f l)) n {ls} {as : Sets n ls} →
       (∀ {l} {r : Set l} → F r → r) → Product n (smap f F n as) → Product n as
palg f F zero    alg ps       = _
palg f F (suc n) alg (p , ps) = alg p , palg f F n alg ps

liftₙ : ∀ k n {ls rs} {as : Sets n ls} {bs : Sets k rs} {r} {b : Set r} →
        Arrows k bs b → Arrows k (smap _ (Arrows n as) k bs) (Arrows n as b)
liftₙ k n op = curryₙ k λ fs →
               curryₙ n λ vs →
               uncurryₙ k op $
               palg _ _ k (λ f → uncurryₙ n f vs) fs

-- implication

infixr 6 _⇒_
\end{code}
%<*implication>
\begin{code}
_⇒_ : Arrows n {ls} as (Set r) → Arrows n as (Set s) →
      Arrows n as (Set (r ⊔ s))
_⇒_ = lift₂ _ (λ A B → (A → B))
\end{code}
%</implication>
\begin{code}

-- conjunction

infixr 7 _∩_
\end{code}
%<*conjunction>
\begin{code}
_∩_ : Arrows n {ls} as (Set r) → Arrows n as (Set s) →
      Arrows n as (Set (r ⊔ s))
_∩_ = lift₂ _ (λ A B → (A × B))
\end{code}
%</conjunction>
\begin{code}

-- disjunction

infixr 8 _∪_
\end{code}
%<*disjunction>
\begin{code}
_∪_ : Arrows n {ls} as (Set r) → Arrows n as (Set s) →
      Arrows n as (Set (r ⊔ s))
_∪_ = lift₂ _ (λ A B → (A ⊎ B))
\end{code}
%</disjunction>
\begin{code}

-- negation

infix 9 ¬_
\end{code}
%<*negation>
\begin{code}
¬_ : Arrows n {ls} as (Set r) → Arrows n as (Set r)
¬_ = liftₙ 1 _ (λ A → (A → ⊥))
\end{code}
%</negation>
\begin{code}
