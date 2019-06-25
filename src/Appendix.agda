open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

cong : ∀ {a b} {A : Set a} {B : Set b} {x y : A} →
       (f : A → B) → x ≡ y → f x ≡ f y

cong f refl = refl

_ : 2 + 3 ≡ 5
_ = refl

id : ∀ {l} {A : Set l} → A → A
id x = x
