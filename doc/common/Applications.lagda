\begin{code}
module Applications where

open import Level using (Level; _⊔_)
open import StateOfTheArt
  using ( List; []; module Listy
        ; _,_; uncurry; curry
        ; tt
        )
open Listy
open import N-ary
open import Data.Nat.Base using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst)
open import Function using (_∘_; flip; _$_)

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
-- n-ary versions of `cong` and `subst`
-- (See below for the refactored versions merged into the stdlib)


module OLD where

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
           (P Q : Arrows n as (Set r)) → Set (r ⊔ (⨆ n ls))
  Substₙ zero     P Q = P → Q
  Substₙ (suc n)  P Q = ∀ {x y} → x ≡ y → Substₙ n (P x) (Q y)
\end{code}
%</Subst>
\begin{code}

\end{code}
%<*subst>
\begin{code}
  substₙ : ∀ {n r ls} {as : Sets n ls} →
           (P : Arrows n as (Set r)) → Substₙ n P P
  substₙ {zero}   P x     = x
  substₙ {suc n}  P refl  = substₙ (P _)
\end{code}
%</subst>
\begin{code}


------------------------------------------------------------------------
-- Refactored n-ary versions of `cong` and `subst` using `Equalₙ`

\end{code}
%<*refactoredcong>
\begin{code}
module _ n {ls} {as : Sets n ls} {R : Set r} (f : Arrows n as R) where

  g : Product n as → R
  g = uncurryₙ n f

  congₙ : ∀ {l r} → Arrows n (Equalₙ n l r) (g l ≡ g r)
  congₙ = curryₙ n (λ eqs → cong g (fromEqualₙ n eqs))
\end{code}
%</refactoredcong>
\begin{code}

\end{code}
%<*refactoredsubst>
\begin{code}
module _ {n ls} {as : Sets n ls} (P : Arrows n as (Set r)) where

  Q : Product n as → Set r
  Q = uncurryₙ n P

  substₙ : ∀ {l r} → Arrows n (Equalₙ n l r) (Q l → Q r)
  substₙ = curryₙ n (λ eqs → subst Q (fromEqualₙ n eqs))
\end{code}
%</refactoredsubst>
\begin{code}

------------------------------------------------------------------------
-- N-ary zipWith

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


\end{code}
