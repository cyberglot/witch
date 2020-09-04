module Witch.Effects.CPSStaged where

import Witch.Effects.CPSUnstaged as Unstagged

open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.Nat using (ℕ; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_)
open import Data.String using (_++_; show)
open import Function using (id; _$_)


data Exp : Set → Set₁ where
  Ł : {a b : Set} → (Exp a → Exp b) → Exp (a → b)
  _∙_ : {a b : Set} → Exp (a → b) → Exp a → Exp b


-- pretty : {a : Set} → ℕ → Exp a → String
-- pretty s (Ł f) = "(λ x" ++ show s ++ " => " ++ pretty (s + 1) (f (Var ("x" ++ show s))) ++ ")"
-- pretty s (f ∙ x) = "(" ++ pretty s f ++ " " ++ pretty s x ++ ")"

CPS : Set → Set → Set
CPS r a = (Exp a → Exp r) → Exp r

shift0 : {a r : Set} → ((Exp a → Exp r) → Exp r) → CPS r a
shift0 = id

runIn0 : {a r : Set} → CPS r a → (Exp a → Exp r) → Exp r
runIn0 = id

reset0 : {a : Set} → CPS a a → Exp a
reset0 m = runIn0 m id

pure : {a r : Set} → Exp a → CPS r a
pure a = \k → k a

push : {a b r : Set} → (Exp a → CPS r b) → (Exp b → Exp r) → (Exp a → Exp r)
push f k = \a → f a k

bind : {a b r : Set} → CPS r a → (Exp a → CPS r b) → CPS r b
bind m f = \k → m (push f k)

_>>=_ : {a b r : Set} → CPS r a → (Exp a → CPS r b) → CPS r b
_>>=_ = bind

reify : {a b r : Set} → CPS r a → Exp (Unstagged.Cps r a)
reify m    = (Ł $ \ k →  m (\a → k ∙ a))

reflect : {a r : Set} → Exp (Unstagged.Cps r a) → CPS r a
reflect m  = \k → m ∙ ((Ł $ \ a →  k a))

app : {a b r : Set} → CPS r (a → Unstagged.Cps r b) → CPS r a → CPS r b
app mf ma = do
  f ← mf
  a ← ma
  reflect (f ∙ a)

lam : {a b r : Set} → (Exp a → CPS r b) → CPS r (a → Unstagged.Cps r b)
lam f = pure ((Ł $ \ a →  reify (f a)))

resumeTwice : CPS ℕ (ℕ → Unstagged.Cps ℕ ℕ)
resumeTwice = lam (\n → shift0 (\c → c (c n)))
