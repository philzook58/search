module Rel where


import Data.Tuple (swap)
import Control.Arrow (second)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (mapMaybe)
import Data.List (nub)
-- http://hackage.haskell.org/package/relation-0.2.1/docs/Data-Relation.html
{-
data Relation a b  = Relation { domain ::  M.Map a (S.Set b)
                                , range  ::  M.Map b (S.Set a)
                                } deriving (Show, Eq, Ord)


Query optimization in database systems is related. A search strategy based on what is available. If stuff, isn't indexed, try to avoid building them
unless it is useful.
Different tables have different indices avaiable

Hash join ~~ kind of what we're doing with maps
http://hackage.haskell.org/package/unordered-containers-0.2.10.0/docs/Data-HashSet.html
HashSet and hashMap are effectively drop ins that require hashable rather than Ord
Sort merge join - I haven't implemented that. Could though. The AscList interface, which should probablyt be protected by a newtype
https://www.twanvl.nl/blog/haskell/generic-merge
interesting. merge as a kind of fold which selects which
http://hackage.haskell.org/package/vector-algorithms-0.8.0.1


Database system,s in general is highly related. We could probably directly intepret to SQL queries. (point free sql?)


If profunctor is relations, Do the free converse?
data Converse p a b = { p b' a', b' -> b, a -> a' }
Converse (Converse p) <-> p

profunctor inequality
(p a b) ~~ (q a b, r a b)
this is lens


Compose makes sense.
Rift from profunctors does appear to be related to the right division of relations.
data Meet p a b = (p a b, p a b) -- just guesses. The Meet is also bviously a profunctor.
data Join p a b = Either (p a b) (p a b) 
WrapBi b p = b (p a b) (p a b)
WrapBi b p q = b (p a b) (q a b) is a profunctor

Ends and coends. Are about diagonal-ish relations.  Diagonal over types though. Still, the identity relationship, projectors


How to deal with non algebraic data types?
Int, float
Abstract domains?
guard ?


Rel (a,b,c) (d,e) = Map a (Map b (Map c (Map d))) -- completely curry. trans untrans cheap. Swap isn't awful. Compose filters a bit. Converse very expensive

-}
--compose :: Relation b c -> Relation a b -> Relation a c
-- compose 


-- The simplest possible type. Inefficient, but works for many purposes
type Rel a b = [(a,b)]
type Rel' a b =  (M.Map a (S.Set b)) -- even this is denormalizing. Can get empty sets in result. We really want M.Map a (NonEmptySet b)
-- data Iso a b = {to :: a -> b, from :: a -> b}
-- data IsoFin a b = {to :: M.Map a b, from :: M.Map b a}
-- data FunRel {a -> [b],  b -> [a]}

-- categorical instances. Require typeclass constraint, so not actual Category instances.
-- nested loop join
compose :: Eq b => Rel a b -> Rel b c -> Rel a c
compose xs ys = [ (a,c)  | (a, b) <- xs, (b', c) <- ys, b' == b]

idRel :: (Enum a, Bounded a) => Rel a a
idRel = liftSet enumAll


-- Relation specific operators

-- meet?
intersect :: (Eq a, Eq b) => Rel a b -> Rel a b -> Rel a b
intersect xs ys = [x | x <- xs, x `elem` ys]

converse :: Rel a b -> Rel b a
converse = fmap swap

lambda :: Eq a => Rel a b -> (a -> [b]) -- converts relation into alternative form, "power tranpose" operator
lambda xs x = [ b | (x',b) <- xs, x' == x]

transform :: (Ord a, Ord b) => Rel a b -> (M.Map a (S.Set b)) -- Rel' a b
transform rel = M.fromListWith S.union (map (second S.singleton) rel) -- One way of doing it. Should be a better way

transform' :: (Ord a, Ord b) => (M.Map a (S.Set b)) -> Rel a b
transform' rel = [ (a,b)  | (a, s) <- M.toList rel, b <- S.toList s]


compose' :: (Ord a, Ord b, Ord c) => Rel' a b -> Rel' b c -> Rel' a c -- can result in maps to empty set. maybe want to trim those to maintain invariant.
compose' r1 r2 =  (M.map S.unions) (partialcompose r1 r2)  -- M.map (\sb -> S.unions $ mapMaybe (flip M.lookup r2) $ S.toList sb) r1

partialcompose :: (Ord a, Ord b, Ord c) => Rel' a b -> Rel' b c -> M.Map a [S.Set c] 
partialcompose r1 r2 = M.map (\sb -> mapMaybe (flip M.lookup r2) $ S.toList sb) r1


converse' :: (Ord a, Ord b) => Rel' a b -> Rel' b a
converse' =  transform . converse . transform'   -- M.foldrWithKey   (\k sk' m ->  \k' -> M.adjust (S.insert k)  m )   M.empty  rel 


join :: (Ord a, Ord b) => Rel' a b -> Rel' a b -> Rel' a b
join = M.unionWith S.union

meet :: (Ord a, Ord b) => Rel' a b -> Rel' a b -> Rel' a b
meet = M.intersectionWith S.intersection
{-
rdiv :: Rel 
rdiv x y = [  (c,a) | (c,a) <- top, all [   | (a',b) <- y, a == a', (c',b') <- x, b == b', c == c']   ]
datajoin x y = = [ (a,b,c) | (a,b) <- x, (b', c) <- y, b == b'] 
[ (a,c) , [b]  ]

forall f xs = all (map f x) 
-}
-- rdiv x y is maximal relation such that (rdiv x y) . y <= x
rdiv :: (Eq a, Eq b, Eq c) => Rel a c -> Rel b c -> Rel a b
rdiv x y = [ (a,b)  | a <- leftSet x, b <- leftSet y, all (\c -> (a,c) `elem` x && (b,c) `elem` y) (rightSet y)] -- getting the recued candidates from y and x might help.



rsub :: (Eq a, Eq b) => Rel a b -> Rel a b -> Bool
rsub x y = all (flip elem y) x

-- let bs = (map snd y) in let x' = [(c,b) | (c,b) <- xs, b `elem` bs] in let (a,c) `elem` [  ]  
-- collect :: [(a,b)] -> [(a , [b])]
-- we also need to converse the divisor.
-- similarity of compose and divison. One uses intersectionsm, the other unions.
-- I need to think this one over with a cleaer head. Not sure i did it right
rightdiv' :: (Ord a, Ord b, Ord c) => Rel' a c -> Rel' c b -> Rel' a b
rightdiv' g divisor = (M.map intersections) (partialcompose g divisor) where 
                                 intersections (x:xs) = foldr S.intersection x xs 
                                 intersections [] = S.empty -- foldl1 is fishy. List might be empty. Should intersection [] = fullspace?

rightdiv'' :: (Ord a, Ord b, Ord c) => Rel a c -> Rel b c -> Rel a b
rightdiv'' g divisor = transform' $ rightdiv' (transform g) (transform $ converse divisor)

--leftlookup = flip lambda
-- rightlookup = flip (lambda . converse)



included :: (Eq a, Eq b) => Rel a b -> Rel a b -> Bool
included xs ys = (intersect xs ys) == xs


fan :: Eq a => Rel a b -> Rel a c -> Rel a (b,c) 
fan f g = [ (a, (b,c)) | (a,b) <- f, (a',c) <- g, a == a']

fan' ::  Ord a => Rel' a b -> Rel' a c -> Rel' a (b,c)  
fan' = M.intersectionWith outer

outer :: S.Set a -> S.Set b -> S.Set (a,b)
outer sa sb = S.fromDistinctAscList [ (a,b) | a <- S.toAscList sa, b <- S.toAscList sb] -- I think this is right?


par :: Rel a b -> Rel c d -> Rel (a,c) (b,d) 
par f g = [((a,c), (b,d)) | (a,b) <- f, (c,d) <- g] 

-- relational division? complicated operation. 


-- rightdiv :: Rel a c -> Rel b c -> Rel a b
-- rightdiv g j = transform g
{-
forall :: (a -> Bool) -> (b -> Bool) -> Rel a b -> Bool
exists :: (a -> Bool) -> Rel a b -> [b]

forall (c ==) (a ==)
(a,b) <- compose res (converse divisor) -- exists candidates
(leftlookup b divisor) `isSubsetOf` (leftlookup res a)

-- intersect . map (ran j) (dom g)

rightdiv res divisor = [ (a,b) | (b,c) <- divisor, (a,c') <- res, c == c',  c'' <- rightSet divisor   ]

map (\(b,c) -> filter   res  ) divisor 

map (\(b,c) ->    (leftlookup b divisor)) divisor


:: (a -> [c]) -> (c -> [b]) -> (a -> [b])
div g j a = let cs = g a
                bs = map j cs :: [[b]]
                intersect bs
-}



-- this one will be very annoying in the dict language
untrans :: Rel a (b,c) -> Rel (a,b) c
untrans = map assoc where assoc (x,(y,z)) = ((x,y),z)

-- idrel :: E

elemRel :: (Enum a, Bounded a) => Rel a [a]
elemRel = [  (x,p)   | p <- power enumAll, x <- p]

dupRel :: (Enum a, Bounded a) => Rel a (a,a)
dupRel = liftFun dup

fuseRel :: (Enum a, Bounded a) => Rel (a,a) a -- eqRel ?
fuseRel = converse dupRel


-- functional operators
liftFun :: (Enum a, Bounded a) => (a -> b) -> Rel a b
liftFun f = map (second f) idRel

-- tuple doesn't have enum instance? Odd. Is fair interleaving the problem?
allTup :: (Enum a, Bounded a, Enum b, Bounded b) => [(a,b)]
allTup = [(x,y) | x <- enumAll, y <- enumAll]
{-
fairProduct :: [a] -> [b] -> [(a,b)]
fairProduct (x:xs) (y:ys)
-}
-- liftFun2 :: (Enum a, Bounded a, Enum b, Bounded b) => (a -> b -> c) -> Rel (a,b) c
-- liftFun2 = liftFun . uncurry
{-
liftFun2 curry
-}
liftFun2 :: (Enum a, Bounded a, Enum b, Bounded b) => (a -> b -> c) -> Rel (a,b) c
liftFun2 f = [ ((a,b), f a b) |  (a,b) <- allTup ] 

-- Setful operators
power :: [a] -> [[a]]
power (x:xs) = let ps = power xs in (map ((:) x) ps)  ++ ps
power [] = [[]]

enumAll :: (Enum a, Bounded a) => [a]
enumAll = [minBound .. maxBound]

dup x = (x,x)

liftSet :: [a] -> Rel a a
liftSet = map dup

leftSet :: Eq a => Rel a b -> [a]
leftSet = nub . (map fst)

rightSet :: Eq b => Rel a b -> [b]
rightSet = nub . (map snd) -- leftSet . converse

-- predicates
{-
isFunction :: Rel a b -> Bool

isTotal
isIso
is


-}
-- fusion rules

-- The data structures of lifted functions should usually be fused out.



{-
-- ideas

transition to Vector
Map
Set,
Functional forms

make DSL language for manipulation

Make data structure to do relational operations much lazier.

use LogicT somehow

data Rel = Fin [(a,b)] | Top -- represent full relation exlicitly. Bottom is already implicit as []

-}


{-

Finally tagless language integrated query - kiselyov
to my mind he was building the Free Initial value kind of piecemeal?
That's cool for composability, but it seems like this becomes a runtime intepretation? Which sort of kills some of the point of finally tagless
maybe I'm wrong

Annotating things with

Comp :: 
Other ::

Converse ::
Other :: 


Can we overload list comprehension syntax to build a dsl data structre? 

[(a,c) |  <- r,  ] somehow outputs Comp r s


-}