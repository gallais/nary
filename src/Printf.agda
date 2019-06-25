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

data Chunk : Set where
  Nat  : Chunk
  Raw  : String → Chunk

Format : Set
Format = List Chunk

size : Format → ℕ
size []             = zero
size (Nat    ∷ f)  = suc (size f)
size (Raw _  ∷ f)  = size f

0ℓs : ∀ {n} → Levels n
0ℓs {zero}  = _
0ℓs {suc n} = 0ℓ , 0ℓs

format : (fmt : Format) → Sets (size fmt) 0ℓs
format []            = _
format (Nat    ∷ f)  = ℕ , format f
format (Raw _  ∷ f)  = format f

assemble : ∀ fmt → Product _ (format fmt) → List String
assemble []              vs        = []
assemble (Nat    ∷ fmt)  (n , vs)  = show n ∷ assemble fmt vs
assemble (Raw s  ∷ fmt)  vs        = s ∷ assemble fmt vs

printf : ∀ fmt → Arrows _ (format fmt) String
printf fmt = curryₙ (size fmt) (concat ∘ assemble fmt)

lessThan : ℕ → ℕ → String
lessThan = printf (Nat ∷ Raw " < " ∷ Nat ∷ [])

_ : lessThan 2 5 ≡ "2 < 5"
_ = refl


