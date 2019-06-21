{-# LANGUAGE GADTs, NoImplicitPrelude, TypeOperators, DataKinds, FunctionalDependencies, MultiParamTypeClasses, AllowAmbiguousTypes, TypeApplications, 
PolyKinds, FlexibleInstances, RankNTypes, ScopedTypeVariables #-}

module PointFree where
import Control.Arrow
import Control.Category
import Prelude hiding (id, (.))
import Data.Proxy

-- maybe I should be defining these via singletons promotion
type a :+: b = Either a b
type a :*: b = (a,b)
type f <<< g = 'Comp g f
type f >>> g = 'Comp f g
type f *** g = Par f g
type f &&& g = 'Fan f g
type f ||| g = 'Split f g
-- type f +++ g = 

-- Do it this way or in this style
-- Singletons won't autogenerate thse because I want the actual function held.
-- Its will generate other stuff though. 

{- These are the singletonized versions of regular |||
(%|||) :: TFun f -> TFun g -> TFun (Split f g)
(TFun f) %||| (TFun g) = TFun 

I dunno
type l ::: a b = TFun l (a -> b)

lft :: TFun 'Lft a (a :+: b)
lft = TFun Left
rgt
dump = TFun (const ())
absurd :: 
absurd = TFun absurd

instance ProFunctor TFun l where -- nvm. no this blows a hole wide open into it
    bimap f g (TFun h) = 

data LawProof where
    Law1 :: (a ||| b)  (yada yada)




-}

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
    
type Par f g = Fan (Comp f Fst) (Comp g Fst) 

type NatF a = () :+: a


type T1 = 'Comp 'Fst 'Snd



class Reflect a b | a -> b where
    reflect :: b
-- I guess reflect is exactly the same as the interpeter. However, as type class based dispatch, we can be pretty sure there is no overhead.
instance Reflect ('Fst :: PF (a,b) a) ((a,b) -> a) where -- it is bizarre that I can reflect kinds like this. TypeInType?
    reflect = fst
instance Reflect ('Snd :: PF (a,b) b) ((a,b) -> b) where
    reflect = snd
-- alternate style is to use newtype wrapped functions phantom tagged with their contents

preflect :: forall a b. Reflect a b => Proxy a -> b
preflect _ = reflect @a

succ :: PF a (NatF a)
succ = Rgt
zero :: PF b (NatF a)
zero = Comp Lft Dump

type ListF b a = () :+: (b :*: a) 
-- nilF, consF
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


{-

rewrite search.
How to express rewrite rules?
pattern match gives you kind of a hoas for rewriting.

Can pattern match in typeclass more thoroguhly.
or type families



-}

{-
Algebra of Types
Linear algerba of types

Isomorhpisms classes of types -> gives commutiativity and distributivty axioms.

Iso' (a,b) (b,a)
Iso' (a, b :+: c) (a :*: b :+: a :*: c )
Iso' (a :+: b) (b :+: a)
Iso' (Zero :+: a) a
Iso' (One :*: a) a
Iso' (Zero :*: a) Zero

types form a semiring modulo ispmorphisms
type aprametrzied types are analogs of polynomials

Types are more analgous to the non-negative integers. "Negative" types are an exotic thing.

one can construct a Ring of types via a tuple + equivalence relation analgous to rationals
data a :-: b = Minus a b
type family (:+:) 
   (a :-: b) :+: (c :-: d) = (a :+: c) :-: (b :+: d)

Iso is roughly equality. (equivalence relation at least)
A notion of inequality can be derived out of Prism and Lens
 a <= b -> a <= b + c

something like this.
Prism c a ~ exists b. Iso c (a + b)
Lens c a ~ exists b Iso c (a,b)

Prism is really <=. 
Lens is something else. Divisibility? a | b  if a ~ b*c
traversal is somehow a superset of these. Polynomial relation? p is polynomial in a (a fairly void statement since you don't even have to use a)
It is hard to see how something could NOT be polynomial in something else?
However, Traverse a b, Traverse b c, implieces a Traverse a c, however, therse is no direct dependence of a on c if polymorphic?
"Is polynomial in" is a transitive relation

Considering types modulo isomorphisms, they are all isomorphic to just finite types of the different sizes.
Hence wesort of have peano arithmetic.
Including inifinite types or type parameters for realz expands what you are talking about.

forall x. Lens ((x,x)+2x+1) (x+1) -- demontrates that x+1 is a factor of x^2 + 2x+1
-- proof will consist of factoring via isomorphisms (using distrubutive law in reverse)

base lens combinators need to be considered axioms, or could do in agda and carry lens laws along with lens

a -> b == b^a. But this is just shorthand for finite types a. You're going into transcendetal equations if you let a be variable, not polynomials



-- point free "singletons"

newtype SFun l a b = SFun (a -> b)
newtype SFun (l :: a -> b) = SFun (a -> b)
-- our axiom set
SFun 

data SFun' a b where -- GADTs for lifting. But not quite the regular singleton story since we'll be 
    Comp ::


data Converse? Should we allow converse? Maybe build a type class that can't strip converse wrappers

data Comp a b
compose :: SFun l' b c -> SFun l a b -> SFun (Comp l' l) a c
compose (SFun f) (SFun g) = SFun (f . g)


fan :: SFun l -> SFun l' -> (Fan l l')
dup
split
par
|||


We need the totally unapplied symbols.
We need to write point-free programs at the type level.
SndSym0
FstSym0



-}