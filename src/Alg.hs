{-# LANGUAGE TypeOperators, RankNTypes, TypeFamilies, NoStarIsType, TupleSections, 
LambdaCase, EmptyCase, MultiParamTypeClasses, FunctionalDependencies, TypeApplications, 
ScopedTypeVariables, TypeSynonymInstances, FlexibleInstances,  UndecidableInstances,  DataKinds #-}
module Alg where

import  Control.Lens
import Control.Arrow
import Data.Void

type a * b = (a,b)
type a + b = Either a b
type b ^ a = a -> b
type O = Void
type I = ()
-- I'm a Naughty boy. Needs NoStarIsType.





-- http://hackage.haskell.org/package/base-4.12.0.0/docs/src/GHC.TypeNats.html#%2A
-- check out typelits for more
infixl 6 + -- ((a + b) + c)
infixl 7 *
infixr 8 ^


-- derived definitions
type Succ a = I + a
type Two = Succ I
type Three = Succ Two
type Four = Succ Three

-- alternative hierarchy
type One = Succ O

{-
Isomorphisms have an identity and compose. They form a category
id :: Iso' a a
(.) :: Iso' b c -> Iso' a b -> Iso' a c
-}

-- isomorphisms can also be reversed. from is the name of this combinator from Control.Lens.Iso
rev :: Iso' a b -> Iso' b a
rev = from

-- a very simple proof. holds basically by definition
oneonetwo :: Iso' (I + I) Two
oneonetwo = id

type a ~~ b = Iso' a b


-- now we start to state our axioms
-- interestingly, I believe the Iso and Lens laws to follow actually follow via parametricity.

-- associativity + a identity object make mul and plus a monoid
plus_assoc :: Iso' (a + (b + c)) (a + b + c)
plus_assoc =  iso assoc unassoc  where
                   assoc (Left a) = Left (Left a)
                   assoc (Right (Left b)) = Left (Right b)
                   assoc (Right (Right c)) = Right c
                   unassoc (Left (Left a)) = Left a
                   unassoc (Left (Right b)) = Right (Left b)
                   unassoc (Right c) = (Right (Right c))

mul_assoc :: Iso' (a * (b * c)) (a * b * c)
mul_assoc =  iso (\(a,(b,c)) -> ((a,b),c)) (\((a,b),c) -> (a,(b,c)))


-- could also use `absurd` from Data.Void for empty case/. Could also use EmptyCase syntax
id_plus :: Iso' (a + O) a
id_plus = iso (\case Left x -> x
                     Right x -> absurd x) Left

id_mul :: Iso' (a * I) a
id_mul = iso (\(x,_) -> x) (\x -> (x,()))


-- they are also commutative
-- specialized version of swapped from Control.Lens.Iso for future clarity
comm_plus :: Iso' (a + b) (b + a)
comm_plus = swapped
comm_mul :: Iso' (a * b) (b * a)
comm_mul = swapped



--type Test a b c = (a * b + a * c)
-- The distributive property and the zero*x=zero property make the type algebra a semiring.

-- I don't see this one in Lens. Maybe it is there though?
-- distributive property
dist :: Iso' (a * (b + c)) (a * b + a * c)
dist = iso (\(a,bc) -> (a,) +++ (a,) $ bc) (\case Left (a,b) -> (a, Left b)
                                                  Right (a,c) -> (a, Right c))   

mul_zero :: Iso' (a,O) O
mul_zero = iso (\(_,y) -> absurd y) absurd

-- Those are our basic laws.

-- a more complicated proof
twotwofour :: Iso' (Two + Two) Four
twotwofour = lemma1 . lemma2 where
             lemma1 :: Iso' (Two + Two) (I + Three)
             lemma1 = rev plus_assoc
             lemma2 :: Iso' (I + Three) Four -- a definition actually
             lemma2 = id

-- a specialized version of firsting and seconding for clarity
lefting :: (a ~~ b) -> (a + c) ~~ (b + c)
lefting = firsting

righting :: (a ~~ b) -> (c + a) ~~ (c + b)
righting = seconding


-- very painful. Using holes _ and error messages absolutely essential
factorexample ::  ((a + I) * (a + I)) ~~ (a * a + Two * a + I)
factorexample = dist .  -- distribute out the right side 
               (lefting (comm_mul . dist)) . -- in the left sum term distribute out
               (righting (comm_mul . dist)) . -- in the right sum term distribute out
                plus_assoc . -- reassociate plus to the left
               (lefting (lefting (righting comm_mul))) . -- turn a * I term to I * a
                (lefting (rev plus_assoc)) . -- associate the two a*I terms together into an (a * I + a * I) term 
                 (lefting (righting (rev lemma))) . -- factor together that subterm into Two * a
                  (righting id_mul) where -- convert last I * I term into I
    lemma ::   ((b + c) * a) ~~ (b * a + c * a)
    lemma = comm_mul . dist . (lefting comm_mul) . (righting comm_mul)


ldist ::   ((b + c) * a) ~~ (b * a + c * a)
ldist = comm_mul . dist . (lefting comm_mul) . (righting comm_mul)

-- (lefting dist) . _
-- a newtype to mark variable position
newtype V a = V a

-- typical usage, bind the V in a unification predicate to keep expression clean
-- (V a' ~ a, V b' ~ b) => (a + b) * b 

-- a phantom labelled newtype for variable ordering. 
newtype VL l a = VL a





{-
Suggested typeclasses maybe want to make them 

Expand -- take to sum of product form
Simplify -- absorb I and O.
SortProd -- put each proeduct
SortSum
RightAssoc

canonical = expand, simplify, sort
(rewrite @a @b) = (rev (canonical @a)) . (canonical @b) 

-}

class Expand a b | a -> b where
    expand :: Iso' a b
instance (Expand a a', Expand b b', Expand c c') => Expand (a * (b + c)) (a' * b' + a' * c') where
    expand = (firsting (expand @a)) . (seconding ((lefting (expand @b)) . (righting (expand @c)))) . dist 
instance (Expand a a', Expand b b', Expand c c') => Expand ((a + b) * c) (a' * c' + b' * c') where
    expand = (seconding (expand @c)) . (firsting ((lefting (expand @a)) . (righting (expand @b)))) . ldist 
instance (Expand a a', Expand b b') => Expand (a + b) (a' + b') where
    expand = (lefting (expand @a)) . (righting (expand @b))
--instance (Expand a a', Expand b b') => Expand ((a * b) * c) (a' + b') where
--    expand = (lefting (expand @a)) . (righting (expand @b))
instance Expand O O where
    expand = id
instance Expand I I where
    expand = id
instance Expand (V a) (V a) where
    expand = id


-- http://www.philipzucker.com/a-touch-of-topological-quantum-computation-in-haskell-pt-ii-automating-drudgery/
-- gosh I guess I'm really smart
{-
class RightAssoc a b | a -> b where
    rightAssoc :: Iso' a b
instance (RightAssoc ((a + b) + c) abc') => RightAssoc (a + (b + c)) abc' where
    expand = (firsting (expand @a)) . (seconding ((lefting (expand @b)) . (righting (expand @c)))) . dist 
instance RightAssoc (a + b) ab' => RightAssoc ((a + b) + c)
instance RightAssoc O O where
    rightAssoc = id
instance RightAssoc I I where
    rightAssoc = id
instance RightAssoc (V a) (V a) where
    rightAssoc = id
-}

class PullLeft a b | a -> b where
   pullLeft :: a ~~ b
instance PullLeft O O where
    pullLeft = id
instance PullLeft I I where
    pullLeft = id
instance PullLeft (V a) (V a) where
    pullLeft = id
instance PullLeft (f O b) (f O b) where -- abstract over both + and *
    pullLeft = id
instance PullLeft (f I b) (f I b) where
    pullLeft = id
instance PullLeft (f (V a) b) (f (V a) b) where
    pullLeft = id
instance (PullLeft a a')  => PullLeft ((a + b) + c) (a' + (b + c)) where
    pullLeft = (rev plus_assoc) . (lefting pullLeft)
instance (PullLeft a a')  => PullLeft ((a * b) * c) (a' * (b * c)) where
    pullLeft = (rev mul_assoc) . (firsting pullLeft)

-- peano operations?
{-
class Canon a b | a -> b where
   canon :: a ~~ b
instance Canon O O where
    canon = id
instance Canon I I where
    canon = id
    {-
instance (Canon x x', Canon y y') => Canon (x * y) where
    canon =
    -} 
instance Canon (O * x) O where
    canon = comm_mul . mul_zero
instance Canon (x * O) O where -- why is this not overlapping?
    canon = mul_zero
instance Canon x x' => Canon (x * I) x' where
    canon = id_mul . canon
instance Canon x x' => Canon (I * x) x' where
    canon = comm_mul . id_mul . canon
instance (Canon (x * z) xz, Canon (y * z) yz) => Canon ((x + y) * z) (xz + yz) where
    canon = ldist . (lefting canon) . (righting canon)

instance Canon (y + (I + x)) z => Canon ((I + y) + x) z where
    canon = (lefting plus_comm) . (rev plus_assoc) . canon
instance Canon x x' => Canon (O + x) x' where
    canon = comm_plus . id_plus . canon
-}



type family BaseCase a where
   BaseCase I = 'True
   BaseCase O = 'True
   BaseCase (V _) = 'True
   BaseCase _ = 'False

class Simplify a b where
    simplify :: a ~~ b
instance Simplify O O where
    simplify = id
instance Simplify I I where
    simplify = id
instance {-# OVERLAPPABLE #-} (Simplify x x', Simplify y y') => Simplify (x * y) (x' * y') where -- these two could be combined
    simplify = (firsting simplify) . (seconding simplify)
instance (Simplify x x', Simplify y y') => Simplify (x + y) (x' + y') where
    simplify = (lefting simplify) . (righting simplify)
instance {-# INCOHERENT #-}  Simplify (O * x) O where
    simplify = comm_mul . mul_zero
instance {-# INCOHERENT #-}  Simplify (x * O) O where -- why is this not overlapping?
    simplify = mul_zero
instance {-# INCOHERENT #-} Simplify x x' => Simplify (x * I) x' where
    simplify = id_mul . simplify
instance {-# INCOHERENT #-} Simplify x x' => Simplify (I * x) x' where
    simplify = comm_mul . id_mul . simplify
instance Simplify x x' => Simplify (x + O) x' where
    simplify = id_plus . simplify
instance Simplify x x' => Simplify (O + x) x' where
    simplify = comm_plus . id_plus . simplify
instance (Simplify (x * z) xz, Simplify (y * z) yz) => Simplify ((x + y) * z) (xz + yz) where
    simplify = ldist . (lefting simplify) . (righting simplify)
instance (Simplify (a * b) ab, Simplify (a * c) ac) => Simplify (a * (b + c)) (ab + ac) where
    simplify = dist . (lefting simplify) . (righting simplify)
thm2 :: (O + I) ~~ I 
thm2 = simplify
thm3 :: (O * I) ~~ O 
thm3 = simplify

-- thm4 :: (Two * Two) ~~ (Two + Two)
-- thm4 = simplify . (rev simplify)
-- thm4 :: (Two + Two) ~~ Four

class Peano a b | a -> b where
   peano :: a ~~ b

instance Peano I (I+O) where
   peano = rev id_plus
instance Peano O O where
   peano = id
instance (Peano x x', Peano y y') => Peano (x + y) (x' + y') where
   peano = (lefting peano) . (righting peano)
instance (Peano x x', Peano y y') => Peano (x * y) (x' * y') where
   peano = (firsting peano) . (seconding peano)

class EvalPeano a b | a -> b where
   evalpeano :: a ~~ b
instance EvalPeano O O where
    evalpeano = id
instance EvalPeano I I where
    evalpeano = id


instance EvalPeano (V a) (V a) where
    evalpeano = id


instance EvalPeano x x' => EvalPeano (I + x) (I + x') where -- constants evaluate to themselves
    evalpeano = righting evalpeano
instance (EvalPeano x z) => EvalPeano (O + x) z where
    evalpeano = comm_plus . id_plus . evalpeano

-- Try to organize variables in the back
instance (EvalPeano x x') => EvalPeano ((V a) + x) (x' + (V a)) where
    evalpeano = comm_plus . (lefting evalpeano)

--instance (EvalPeano x x', EvalPeano y y',  EvalPeano (x' + (I + y')) z) => EvalPeano ((I + x) + y) z where -- true additions
--    evalpeano = (righting (evalpeano @y)) . (lefting comm_plus) . (rev plus_assoc) . (lefting (evalpeano @x)) . evalpeano
instance (EvalPeano x x',  EvalPeano (x' + (y + z)) r) => EvalPeano ((x + y) + z) r where -- true additions
    evalpeano = (rev plus_assoc) . (lefting (evalpeano @x)) . evalpeano



instance EvalPeano (O * x) O where
    evalpeano = comm_mul . mul_zero
instance EvalPeano (I * x) x where
    evalpeano = comm_mul . id_mul
instance (EvalPeano x x', EvalPeano (x' * (y * z)) r) => EvalPeano ((x * y) * z) r where
    evalpeano = (rev mul_assoc) . firsting evalpeano . evalpeano
instance (EvalPeano (x * z) xz, EvalPeano (y * z) yz, EvalPeano (xz + yz) r) => EvalPeano ((x + y) * z) r where
    evalpeano = ldist . (lefting evalpeano) . (righting evalpeano) . evalpeano

instance (EvalPeano x x') => EvalPeano ((V a) * x) (x' * (V a)) where
    evalpeano = comm_mul . (firsting evalpeano)


thm4 :: (Two + Two) ~~ Four
thm4 = evalpeano -- . (rev (peano . evalpeano))

thm5 :: (Two * Two) ~~ Four
thm5 = evalpeano

thm6 :: (Two * Two) ~~ (Two + Two)
thm6 = evalpeano . (rev evalpeano)

thm7 :: (Two * Three) ~~ (Two + Two * Two)
thm7 = evalpeano . (rev evalpeano)


-- intended to be used in the type directed form `rewrite @intermediate_type`
rewrite :: forall b a c. (EvalPeano a c, EvalPeano b c) => a ~~ b
rewrite = evalpeano . (rev evalpeano)

-- factorexample' :: (V a' ~ a) => (I * (a + I)) ~~ _ -- * (a + I)) ~~  _ -- (a * a + Two * a + I)
-- factorexample' = evalpeano -- . (rev evalpeano)


{-


Good lord this has ended up being more painful than I expected.

Prism = inequality
Lens = divisibility


-}

type a >= b = Prism' a b
type a .| b = Lens' a b

-- once again, these are true via parametricity, more or less
one_div :: a .| I 
one_div = lens (const ()) const

zero_lte :: a >= O
zero_lte = prism' absurd (const Nothing)

zero_div :: O .| a
zero_div = lens absurd const

{-

the core combinators from the lens library are

_1 :: (a,b) .| a
_2 :: (a,b) .| b

_Left :: (a + b) >= a
_Right :: (a + b) >= b


-}


twodiv4 :: (Two * Two) .| Two
twodiv4 = _1

onelesstwo :: Two >= I
onelesstwo = _Left

-- Iso can be composed with Lens and Prism and stay a Lens or Prism.
-- This corresponds with you can compose isomorphisms with either inequalities or divisiblity
factorexample'' ::  (a * a + Two * a + I) .| (a + I)
factorexample'' = (rev factorexample) . _1 

-- maybe we want to newtype these.
-- partially applied +
type P n = (Either n) 
-- partially applied *
type M n = (,) n

type LowerP f = f O
-- you can lower back to the original form
unP :: LowerP (P n) ~~ n
unP = id_plus

type LowerM f = f I
-- you can lower back to the original form
unM :: LowerM (M n) ~~ n
unM = id_plus

-- Now addition is defined as Functor.Compose
-- add_good :: (Compose (P n) g) a ~~ (n + g) a
-- add_good = id  -- needs newtype iso.



-- negative numbers
-- illegal polymorphic type. no impredicative polymorphism
type T g a b = (a >= (g b))
newtype GTE a b = GTE (a >= b)
--newtype N g f = N { unN :: forall a b. (((g a) >= b ) ~~ (a >= f b))}
-- this is accepted
-- This is the proof term that f is the negative of g
type N g f = forall a b. ((GTE (g a) b) ~~ (GTE a (f b)))

-- ordinarily we think of negative numbers as being (n + (-n) == 0), but this makes no sense.
-- The inequality version does (maybe). f will have to be a type family, not type.
-- yeah, myabe this is bunkus. could make it polymorphic on only on a? And pick b such that 

-- we can define an interesting version of the negative numbers
-- it doesn't feel so intrinsic anymore though.
-- also going higher order on the prisms is odd.



-- similarly for multiplication
-- using divisibility rather than GTE
