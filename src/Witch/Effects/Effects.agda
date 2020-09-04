module Witch.Effects.Effects where

open import Ataca.Core using (Tac)
open import Prelude

data Free (C : Set) (R : C → Set) (A : Set) : Set where
  ret  : A → Free C R A
  bind : (c : C) → (R c → Free C R A) → Free C R A

pure : ∀ {C R A} → A → Free C R A
pure = ret

_>>=_ : ∀ {C R A B} → Free C R A → (A → Free C R B) → Free C R B
ret x    >>= k = k x
bind c f >>= k = bind c (λ r → f r >>= k)

data Effect : Set where
  proof-search : Effect
  tactics      : {a : Set} → Tac a → Effect
  smt          : Effect
  state        : Effect
  exception    : Exception → Effect

data InternalSt : Set where
  proof-state : InternalSt
  goal        : InternalSt
  term        : InternalSt
  env         : InternalSt

data Exception : Set where
  tactic-fails : Exception

witch : Effect → TC.Tactic
witch proof-search = TC.newMeta
witch (tactics t)  = Tac.runT t
witch smt          = TC.newMeta
witch state        = TC.newMeta
witch expection    = TC
