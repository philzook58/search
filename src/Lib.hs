module Lib where
import Control.Monad (guard)
import Data.Foldable
someFunc :: IO ()
someFunc = putStrLn "someFunc"

asNumber :: [Int] -> Int
asNumber = foldl' (\t o -> t*10 + o) 0
to_number = asNumber

digits = [0.. 9]
-- and f g x = (f x) && (g x) 
remove _ [] = []
remove xs (y:ys) | (y `elem` xs) = remove xs ys
                 | otherwise = y : remove xs ys

sendmoney1 = do
    s <- remove [0] digits
    e <- remove [s] digits
    n <- remove [s,e] digits
    d <- remove [s,e,n] digits
    let send = asNumber [s,e,n,d]
    m <- remove [0,s,e,n,d] digits
    o <- remove [s,e,n,d,m] digits
    r <- remove [s,e,n,d,m,o] digits
    let more = asNumber [m,o,r,e]
    y <- remove [s,e,n,d,m,o,r] digits
    let money = asNumber [m,o,n,e,y]

    guard (send + more == money)
    return (send,more,money)

solutions = do
    s <- remove [0] digits
    e <- remove [s] digits
    n <- remove [s,e] digits
    d <- remove [s,e,n] digits
    let send = to_number [s,e,n,d]
    m <- remove [0,s,e,n,d] digits
    o <- remove [s,e,n,d,m] digits
    r <- remove [s,e,n,d,m,o] digits
    let more = to_number [m,o,r,e]
    y <- remove [s,e,n,d,m,o,r] digits
    let money = to_number [m,o,n,e,y]
    guard $ send + more == money
    return (send, more, money)

-- https://wiki.haskell.org/Sudoku


{-

https://stackoverflow.com/questions/3757855/how-can-iterative-deepening-search-implemented-efficient-in-haskell

An iterable expansion.
a -> [a]
macthes rewrite rules


beam search -- implciti configuration via reify?
>>= bind instance should prune. Beam n f a. f is a parameter reflecting the optimization criteria? But we need a new one at each new type?
-- could do it as newtype wrapper. Beam sorts a and takes n best ones
(cost x, x)


prune :: Ord b => (a -> b) -> Int -> [a] -> [a]
prune f n = take n $ sortBy f $ nub




iterative search
a*

dynamic programming ~ histomorphism?, futotmorphism? Difference of top down and bottom up?



What is a search?

-}


{-


class (Category k, Ord (k a b)) => Allegory k where
    intersect / lub 
    converse 

class Allegory k => Tabular k

type Rel a b = Set (a,b)
power :: Rel a b -> (a -> Set b)
converse :: Rel a b -> Rel b a
converse = map swap
elem :: Set b -> Rel b (Set b)


compose :: Rel b c -> Rel a b -> Rel a c


isSubsetOf :: Ord a => Set a -> Set a -> Bool

http://hackage.haskell.org/package/relation-0.2.1/docs/src/Data-Relation.html#Relation

Uses an iso like
M.Map a (Set b)
Map b (Set a)
pair


Basically any combination of
Map vs ->
Set vs [] or MonadPlus

Set (a,b)

(a -> Set b, [a])
[(a,b)]
(a -> [b], [a]) -- with invariant that if x not in [a] that f x = []
(a -> [b],    b -> [a],   [(a,b)] ) -- similar invariants.

(a -> [b],    b -> [a],   [(a,b)],   [b],   [a] ) -- similar invariants.

-- sometimes we want to be able to seek or give hints or a predicate.

-- make a typeclass to combine them all. Brings into standard form.
class Relation k where
    lseek :: k a b -> (a -> [b]) 
    rseek :: k a b -> (b -> [a])
    lall :: k a b -> [a]
    rall :: k a b -> [b]
    produce :: k a b -> [(a,b)]


    elem :: (a,b) -> Bool
    in1 :: a -> Bool
    in2 :: b -> Bool

for finite relations these can all be produced automatically. Especially for hashable or Ord types.
databases basically use hashing and ord.

solving sudoku via SQL. solving send more money
make a table for each relation. 
populate with the initially possible values.
join together all the relations.


one could also maintain tables of only the possible values for single cells.
Then merging these around would be a way of propagating information without merging tables to make larger tables.

sudoku
[(Int, Int)] = [(1,1), (2,2), (3,3), (4,4) ..] -- as a projector
[(1,(1,1)), ] -- dup relation. is also an equality projector when applied the other way. dup is dual to equality constraint.
[(Int,Int)] [(1,2), (1,3), ...] as a not equal constraint -- pretty roundabout
[ ( , ) ]

or magic square. Full sudoku is very confusing.

If we make composition actually maintain the seperate relations that compose it seperately, it should perform something like csp.


for inifinite you need to custom make each? What if you write down your relation as an ananmorphism?

class Category k => Relation k where


produce is the most powerful one. None of the others can make produce on their own. produce requires equality to make lseek

produce + eq
lall + lseek = produce


The linear inequalties are infinite relations.
They have metrical and differentiable character, so one might want streams based on that.

    
I'm not inclined to make streams. We need to give guidance at every juncture if we're ever gonna find anything.

MetricRelation k
     proj :: k a b -> (a,b) -> (a,b) -- prohects point to nearby point in relation
     proja :: a -> Maybe b -- finds nearest point with given first part
     proja' :: a -> Maybe (a,b) -- can adjust both but we want a' close to a
     proja'' :: a -> Shape b  -- gives entire region of b that works for a.
     produce :: k a b -> (a,b) -- produce a point in the relation



-- can provide defaults in terms of others often
-- from this can provide composition.
-- hetergenous composition of relation types.
Compsoe :: k a b -> k' b c -> Compose k k' a c
instance Relation k, Relation k' => Relation Compose k k'
   lseek =  (lseek l) >=> (lseek r)
   lall (l, r) = lall l
   rall (l, r) = rall r
   produce =    (rall l)        -- or   (lall r) or fair interleaving of both hoping one will terminate early.

type Rel a b = exists c. (c -> [a], [c], c -> [b]) -- tabular? This also has the feel of an okasaki list or stream?


-- data Relation a b  = Relation { domain ::  M.Map a (S.Set b)
                              , range  ::  M.Map b (S.Set a)
                              }
By using Map, you have the ability to search the domain too. That is why this is different than a -> [b], b -> [a]

The Ord constraint adds a lot of search power beyond brtue force enumeration at the cost of generiucity



Rel a b = {a -> [b], b -> [a]} -- a slight extension on nondeterministic search. There might be oppurtnity for smart caching in the middle.
type Rel a b = Iso a b [b] [a]

data CacheRel a b where
     Compose :: Rel a b -> Set b -> CacheRel b c -> CacheRel a c
     Nil :: CacheRel a b -- can always tell the nil relation. The full relation is harder since we hve to produce values. That's on you dog.

-- is there any reason to hold that Set b. I'm really not sure. I guess you should always use up your cache before pulling more values out of Rel.
-- Smells a little like an okasaki list?

Set a, Set b, a -> [b], b -> [a]?



join :: Set (Set a) -> Set a -- seems straightforward enough. Required for composition.
--roughly something like
compose (f,g) (f',g') = (f >=> f', g' >=> g)
converse (f,g) = (g,f)

cata :: Rel (f a) a -> Rel (Fix f a) a


?

Relations on function spaces. Make DSL data type of pertinent functions

data Fun =
    Cata :: Fun (f a -> a) -> Fun (Fix f a -> a)
    Split :: Fun (a -> c) -> Fun (b -> c) -> Fun (Either a b -> c)
    Fan :: Fun (a -> b) -> Fun (a -> c) -> Fun (a -> (b,c))
    Comp :: Fun (b -> c) -> Fun (a -> b) -> Fun (a -> c)
    Proj1 :: Fun (a,b) -> a
    Proj2 :: Fun (a,b) -> b
    Final :: Fun (a -> ()) -- Maybe just this one isn't a free theorem? Maybe it is from another persepective
    Id :: Fun (a -> a)

    Lit :: String -> (a -> b) -> Fun (a -> b)
    Map :: Fun (a -> b) -> Fun (f a -> f b)
-- no Map also isn't a free theorem. forall f actually implies that a = b like in leibnitz.
-- and that f a -> f b
-- in a universe where we can assume f is polynomial, then it might be free.
-- Generic1 f =>  


instance Arrow (Fun) where
    arr = Lit
    (***) = par
    (&&&) = Fan
    first = Proj1 . 
    second = Proj2 . 

-- arrow fix has completely uncsontrained recursion
class ArrowMap arr1 arr2 where ? Not necessairy even unique

arrowmap1 :: arr1 a b -> arr2 a b -- you can't really have a generic notion of mapping

-- cata does require an endofunctor for algebra. so f makes sense

class CataArrow arr where
    cata :: arr (f a) a -> arr (Fix f a) a

-- hmmm. I am basically making an initial form of the arrow typeclass.
-- if arrows ~ strong profuctors
-- and arrows ~ relations
-- certainly one can in principle lift (actual haskell?) functions to relations

-- https://www.reddit.com/r/haskell/comments/6otigf/are_there_any_plans_to_merge_arrow_and_profunctor/
-- interesting
-- https://elvishjerricco.github.io/2017/03/10/profunctors-arrows-and-static-analysis.html
-- https://bartoszmilewski.com/2016/07/25/profunctors-as-relations/

Maybe profunctors are good start for a pre-relation. Relations can be pre and post composed with functions
HOWEVER. functions do not have converses in haskell. They a teensy bit should from the perspective of relations.
So having a profunctor instance precludes ever having a converse.


-- instances are almost always going to be unsatisfying due to imedance mismatch of the functional character of Haskell.
-- Haskell will give you very little for free except Free.
Category k => Converse k -- 
   converse :: k a b -> k b a




Strong Relations are relations that have the tuple in when 
a relational category (allegory)


everything is all confused.
It is interesting that lens, the canonical actually (invertible, converseable?) concept in Haskell, is a profunctor transformer.
I accept Iso a b as closer to a relation. 



-- we're strongly avoiding currying
-- which I guess isn't so bad... it has laws.
-- Relations don't curry.

-- without currying, we aren't making a functional language. We'll need to build manual "closure objects"?
-- can one make a pure, point-free non-functional language?
  Curry :: 
  Uncurry ::
  App :: Fun (a -> b, a) -> b

-- maybe what we'd prefer is an Applicative Functor instance/ monoidal functor
-- with that in tow we could define a different cata like thing
app :: 
App? :: Fun (f a, f b) -> f (a,b) 
Unit :: Fun () -> f ()



CoApplicative? It's been though about. https://www.reddit.com/r/haskell/comments/qsrmq/coapplicative_functor/
  f (Either a b) -> Either (f a) (f a)

(f (a,b) -> c) )


Generic ~ to / from
data Generic f a = 

plus = Lit "Plus" (uncurry (+))
zerro = Lit "Zero" (const 0)
succ = Lit "Succ" (+ 1)

dup = Fan Id Id
*** f g = Fan (f . Proj1) (g . Proj2) 

-- or really I should be decribing nats inductively
data NatF a = Zero | Succ a -- ~  () + a
type Nat = Fix NatF

-- with monoidal? I need some cobniator that isn't cata?
plus :: (Nat, Nat) -> Nat
plus = (cata phi) . Proj1 where phi = Split (Const Proj2) (Fix . Succ) 
 
-- paramorphism
Para :: Fun (f (Fix f, a) -> a) -> Fun (Fix f -> a)
plus :: (Nat, Nat) -> Nat
plus = para phi where phi = Split 


Dump :: Fun a ()
Impossible :: Fun Void a



-- add one or don't
-- needs distribtute. undist is already definable. odd
 (() + (), Nat) -> Nat
~> (((), Nat) + ((), Nat) -> Nat
 ~> Comp (Split Proj2 (Comp succ Proj2)) Dist

Seems like distribute is a new primitive
also 0 -> (0,a) is a related construct.


chapter 3 of algebra of programming has a lot to say about this.
Tensoiral strength is mentioned as an option. Aren;t all functors strong once you have map?

(NatF NatF NatF (), Nat ) -> Nat, is the type of numbers <= 2 added to a nat.
(Map (Map Strong)) (Map Strong) Strong... uhh, well, with choice at each stage whether to continue to strong or not.


But map is much less powerful if you don't have currying.
Strong :: (f a, b) -> f (a,b)    
strong let's you carry context, storage
 

I'm going to need to strong all the way down to the bottom of a nat.
I think I might be able to derive Dist from Strong. (a, b + c) -> (a, (a, b + c)) -> (a, (a,b) + c) -> (a,b) + (a,c)
If I'm able to Strong +
Not sure it's clear whch strong I meant.
I need BiStrong?

Does seem similar to the appliucative style.
MonoidalMap :: (f a, f b) -> f (a,b) 


Map (a -> b) -> 
BiMap (a -> b) (c -> d) (f a c -> f b d)

BiMap may be useful.  Without currying and functions, there are no contravairant values.
by avoding currying and expoential objects, we reduce the logic we are representing. First order?

if all functors are implicilty poynomial, not clear that Map is necessary. A meta level map may be fine.?

-- BiMap 


NatF (Fix NatF, Nat) -> Nat


-- is this possible or is this a fundmental combinator?
distribute :: (a ,(b + c)) -> (a,b) + (a,c)
distribute = split inl 

-- with currying
plus :: Nat -> Nat -> Nat
plus = cata phi where phi = split id (Fix . Succ)

-- proj1 and proj1 are fine by parametricity
-- actually almost all of them are given by parametricity? Is that the measure of an acceptable combinator?


-- point free gadts?
-- Eq?

plus = Lit "Plus" (uncurry (+))



-- This is also close to a DSL for relations. But the point was to have relations over functions, not an abstract DSL for relations?

    Converse :: Fun (a -> b) -> Fun (b -> a)   -- ? Not sure we want this.  
    Intersect :: Fun a -> b -> Fun a -> b -> Fun a -> b




()
Void
:*:
:+:
:.: -- ?
Fix
type L b a = () :+: (b :*: a)
type N a = () :+: a

*** -- par
&&& -- fan
||| --- split / either
+++ --- plus

swap :: (a,b) -> (b,a)
swap = (par snd fst) . dup

vs 
type N = forall a. () :+: a
type N = \a -> () :+: a


-- makes no sense type Lam a b = forall a'. (a ~ a') => b
type Lam a b = 
type App f a = f a

pointfree lambda for typelevel
type N = 'Fan 'Dump 'Id

-- not sure i need partially applied combinators

type family Apply -- not sure I need this?
  Apply (Fan f g) x = (Apply f x, Apply g x)
  Apply (Dump) x = '()
  Apply Id x = x
  Apply Proj1 (a,b) = a
  Apply Proj2 (a,b) = b
  Apply (Lit f) x = f x 


type L = \(a,b) -> () :+: a :*: b
type L = FanPlus Dump (FanTimes Proj1 Proj2) -- at the type level :+: and :*: are the same thing. They are typelevel pairs.
  Fan Dump Id? if everything is (,)

type L = \a b -> () :+: a :*: b = Curry L1



App
Curry
Uncurry
Fan
Proj1
Proj2
Dump :: ()
-}