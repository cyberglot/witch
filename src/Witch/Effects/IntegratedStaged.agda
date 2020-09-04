-- port from effekt-idris

module Witch.Effects.IteratedStaged where

open import Data.List as List

open import Effects.CpsStaged
open import Effects.IteratedUnstaged

STM : [Set] -> Set -> Set
STM [] a = Exp a
STM (r :: rs) a = (Exp a -> STM rs r) -> STM rs r

pure : Exp a -> STM rs a
pure{  rs= []}         a = a
pure{  rs= r :: rs}  a = \k => k a

push : (Exp a -> STM (r :: rs) b) -> (Exp b -> STM rs r) -> (Exp a -> STM rs r)
push f k = \a => f a k

bind : STM rs a -> (Exp a -> STM rs b) -> STM rs b
bind{  rs= []}         m f = f m
bind{  rs= r :: rs}  m f = \k => m (push f k)

(>>=) : STM rs a -> (Exp a -> STM rs b) -> STM rs b
(>>=) = bind

lift : STM rs a -> STM (r :: rs) a
lift = bind

shift0 : ((Exp a -> STM rs r) -> STM rs r) -> STM (r :: rs) a
shift0 = id

runIn0 : STM (r :: rs) a -> (Exp a -> STM rs r) -> STM rs r
runIn0 = id

reset0 : STM (a :: rs) a -> STM rs a
reset0 m = runIn0 m pure

mutual
  reify : STM rs a -> Exp (Stm rs a)
  reify {rs = []} m = m
  reify {rs = (q :: qs)} m =
    (Lam $ \ k =>  reify (m (\a => reflect {a = q} {rs = qs} (App k  a))))

  reflect : Exp (Stm rs a) -> STM rs a
  reflect {rs = []} m = m
  reflect {rs = (q :: qs)} m =
    \k => reflect (App m  ((Lam $ \ a =>  reify (k a))))

emit : Exp Int -> STM (List Int :: rs) ()
emit {rs} a = shift0 (\c => do
  as <- c Uni
  pure {rs} (Con a as))

emitTwice : Exp Int -> STM (List Int :: List Int :: rs) ()
emitTwice {rs} a =
  bind {rs=List Int::List Int::rs} (emit {rs=List Int::rs} a) (\u =>
  lift {r=List Int} {rs=List Int::rs} (emit a))

export
reifiedEmitTwice : Exp (Int -> Stm [List Int,List Int] ())
reifiedEmitTwice = Lam (\x => reify {rs=[List Int,List Int]} (emitTwice x))

export
reifiedEmitTwice' : Exp (Int -> Stm [List Int,List Int,()] ())
reifiedEmitTwice' = Lam (\x => reify {rs=[List Int,List Int,()]} (emitTwice {rs=[()]} x))
