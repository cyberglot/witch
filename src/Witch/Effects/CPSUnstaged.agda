module Effects.CPSUnstaged where

open import Function using (id)
open import Data.Nat using (ℕ; _+_)

Cps : Set → Set → Set
Cps r a = (a → r) → r

shift0 : {A : Set} {R : Set} → ((A → R) → R) → Cps R A
shift0 = id

runIn0 : {A : Set} {R : Set} → Cps R A -> (A -> R) -> R
runIn0 = id

reset0 : {R : Set} → Cps R R -> R
reset0 m = runIn0 m id

pure : {A : Set} {R : Set} → A -> Cps R A
pure a = \ { k -> k a }

push : {A : Set} {R : Set} {B : Set} → (A -> Cps R B) -> (B -> R) -> (A -> R)
push f k = \ { a -> f a k }

bind : {A : Set} {R : Set} {B : Set} → Cps R A -> (A -> Cps R B) -> Cps R B
bind m f = \ {k -> m (push f k)}

_>>=_ : {A : Set} {R : Set} {B : Set} → Cps R A -> (A -> Cps R B) -> Cps R B
m >>= f = bind m f

example : ℕ
example = 1 + reset0
  (do
    x ← shift0 \ {k → k (k 100)}
    pure (10 + x))
