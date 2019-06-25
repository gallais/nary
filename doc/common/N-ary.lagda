\begin{code}
{-# OPTIONS --without-K --safe #-}

module N-ary where

open import Level using (Level; 0ℓ; _⊔_)
open import StateOfTheArt as Unary
  hiding ( ∃⟨_⟩; ∀[_]; Π[_]; _⇒_; _∩_; _∪_; ¬_
         ; _≡_; refl
         ; map
         ; cong
         ; cong₂
         ; subst
         )
open Listy

open import Data.Nat.Base using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality
open import Function using (_∘_; id; flip; _$_)

private
  variable
    a b c r i j s : Level
    A : Set a
    B : Set b
    C : Set c
    I : Set i
    J : Set j
    R : Set r

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
Sets : ∀ n (ls : Levels n) → Set (Level.suc (⨆ n ls))
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

------------------------------------------------------------------------
-- Pointwise equality for n-ary products

\end{code}
%<*equaln>
\begin{code}
Equalₙ : ∀ n {ls} {as : Sets n ls} →
         (vs ws : Product n as) → Sets n ls
Equalₙ zero     vs        ws        = _
Equalₙ (suc n)  (v , vs)  (w , ws)  = (v ≡ w) , Equalₙ n vs ws
\end{code}
%</equaln>
\begin{code}

-- Pointwise equality implies propositional equality

\end{code}
%</fromequaln>
\begin{code}
fromEqualₙ : ∀ n {ls} {as : Sets n ls} {vs ws : Product n as} →
             Product n (Equalₙ n vs ws) → vs ≡ ws
fromEqualₙ zero     _           = refl
fromEqualₙ (suc n)  (eq , eqs)  = cong₂ _,_ eq (fromEqualₙ n eqs)
\end{code}
%</fromequaln>
\begin{code}

------------------------------------------------------------------------
-- compose function at the n-th position


\end{code}
%<*compose>
\begin{code}
_%=_⊢_ : ∀ n {ls} {as : Sets n ls} → (I → J) →
         Arrows n as (J → B) → Arrows n as (I → B)
zero   %= f ⊢ g = g ∘ f
suc n  %= f ⊢ g = (n %= f ⊢_) ∘ g
\end{code}
%</compose>
\begin{code}

------------------------------------------------------------------------
-- mapping under n arguments

open import Function using (_∘_)

\end{code}
%<*map>
\begin{code}
mapₙ : ∀ n {ls} {as : Sets n ls} →
       (B → C) → Arrows n as B → Arrows n as C
mapₙ zero     f v = f v
mapₙ (suc n)  f g = mapₙ n f ∘ g
\end{code}
%</map>
\begin{code}

\end{code}
%<*focus>
\begin{code}
focusₙ : ∀ n {ls} {as : Sets n ls} →
         Arrows n as (A → B) → (A → Arrows n as B)
focusₙ n f a = mapₙ n (_$ a) f
\end{code}
%</focus>
\begin{code}

\end{code}
%<*congat>
\begin{code}
module _ m n {ls ls'} {as : Sets m ls} {bs : Sets n ls'}
         (f : Arrows m as (A → Arrows n bs B)) where

  private
    f' : Product m as → A → Product n bs → B
    f' vs a ws = uncurryₙ n (uncurryₙ m f vs a) ws

  congAt : ∀ {vs ws a₁ a₂} → a₁ ≡ a₂ → f' vs a₁ ws ≡ f' vs a₂ ws
  congAt {vs} {ws} = cong (λ a → f' vs a ws)
\end{code}
%</congat>
\begin{code}


------------------------------------------------------------------------
-- hole at the n-th position

\end{code}
%<*hole>
\begin{code}
holeₙ : ∀ n {ls} {as : Sets n ls} →
        (A → Arrows n as B) → Arrows n as (A → B)
holeₙ zero     f = f
holeₙ (suc n)  f = holeₙ n ∘ flip f
\end{code}
%</hole>
\begin{code}

------------------------------------------------------------------------
-- function constant in its n first arguments

-- Note that its type will only be inferred if it is used in a context
-- specifying what the type of the function ought to be. Just like the
-- usual const: there is no way to infer its domain from its argument.

\end{code}
%<*const>
\begin{code}
constₙ : ∀ n {ls} {as : Sets n ls} → B → Arrows n as B
constₙ zero     = id
constₙ (suc n)  = const ∘ (constₙ n)
\end{code}
%</const>
\begin{code}

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

-- Warm up: binary version

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

-- Proper n-ary version

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
