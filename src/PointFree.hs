{-# LANGUAGE GADTs, NoImplicitPrelude, TypeOperators #-}

module PointFree where
import Control.Arrow
import Control.Category
import Prelude hiding (id, (.))


type a :+: b = Either a b
type a :*: b = (a,b)

data PF a b where
    Id :: PF a a
    Comp :: PF b c -> PF a b -> PF a c
    Fst :: PF (a,b) a
    Snd :: PF (a,b) b
    Fan :: PF a b -> PF a c -> PF a (b,c)
    Lit :: (a -> b) -> PF a b
    Dump :: PF a ()
    Split :: PF a b -> PF c b -> PF (a :+: c) b
    Lft :: PF a (a :+: b)
    Rgt :: PF b (a :+: b)

type NatF a = () :+: a

succ :: PF a (NatF a)
succ = Rgt
zero :: PF b (NatF a)
zero = Comp Lft Dump

type ListF b a = () :+: (b :*: a) 

nil = Comp Lft Dump
cons :: PF (b, a) (ListF b a)
cons = Rgt

instance Category PF where
    id = Id
    f . g = Comp f g

instance Arrow PF where
    arr = Lit
    (&&&) = Fan
    f *** g = Fan (f . Fst) (g . Snd) 



interp :: Arrow k => PF a b -> (k a b) -- in particular (a -> b)
interp Id = id
interp (Comp f g) = (interp f) . (interp g)
interp Fst = arr fst
interp Snd = arr snd
interp (Lit f) = arr f
interp (Fan f g) = (interp f) &&& (interp g)