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


-}