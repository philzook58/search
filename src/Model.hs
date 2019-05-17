module Model where
import qualified Data.Map.Strict as Map

    -- http://hackage.haskell.org/package/fgl-5.4.2.4/docs/Data-Graph-Inductive-Query-BFS.html
    -- could go with fgl
    -- could go with ST monad

type Transition st = st -> [st]
-- MonadChoice rather than List?
type Prop st = st -> Bool -- st -> Maybe String -- give message about what happened? Nothing if good
type Init st = [st]
{-
search :: [st] -> (st -> Bool) -> (st -> [st]) -> ? 
search init prop step = let initmap = Map.fromList (map (,Nothing) init) in search' initmap init prop step


-- I want an error monad to kill the search as soon as possible.
search'  :: Map.Map st (Maybe st) -> [st] -> (st -> Bool) -> (st -> [st]) -> ? 
search' m frontier prop step = (do  -- ExceptT [] a, ListT (Either String) 
                                  state <- frontier
                                  next_state <- step state
                                  )  

-- This is an State monad
expandfrontier :: [st] -> Map.Map st (Maybe st)  -> ([st], Map.Map st (Maybe st)
expandfrontier frontier m step = let newfront = filter (flip Map.notMember m) (map step) in (newfront, Map.insert )  
[   | st <- frontier  ]

-- There is a state monad with the Map, there is a List monad for nondetemrinism and search and there is and Exception monad for finding violations.
-- State Map.Map (Execpt st [st]) ? Or the reverse? I am a truly shameful haskell programmer.
-}

expandfrontier :: [st] -> (st -> [st]) -> [st]
expandfrontier frontier step = (frontier >>= step)

checkprop :: [st] -> (st -> Bool) -> Either st [st]
checkprop frontier prop = traverse (\st -> if (prop st) then (Right st) else (Left st)) frontier

search :: [st] -> (st -> [st]) -> (st -> Bool) -> Maybe st
search [] step prop =  Nothing
search init step prop =  case (checkprop (expandfrontier init step) prop) of 
                                Left st -> Just st
                                Right sts -> search sts step prop

                          
-- we could speed this up hughes style but screw it.
pathFromMap :: Ord st => st -> Map.Map st (Maybe st) -> [st]
pathFromMap end m = case (m Map.! end) of
                        Nothing -> []
                        Just x -> x : (pathFromMap x m)

-- transition relation combinators

stutter :: (a -> [a]) -> (a -> [a])
stutter f = (\x -> x : (f x))

-- interleave lists
(|||) :: [a] -> [a] -> [a]
[]     ||| ys = ys
(x:xs) ||| ys = x : ys ||| xs

prod :: (a -> [a]) -> (b -> [b]) -> ((a,b) -> [(a,b)])
prod f g = \(x,y) -> [(x',y) | x' <- f x ] ||| [(x,y') | y' <- g y ]

syncprod f g = \(x, y) -> [(x',y') | x' <- f x, y' <- g y]
{-

what will a spec look like:

data State = Open | Closed deriving (Enum, Bounded, Show)

init = [ (x,y) |  x <- [1 .. 7], y <- [5 .. 8], y >= x]

stepx x | x <= 7 = pure $ x + 1 
        | otherwise = [x, x - 1]

-- pluscal analog
data XState = { varx :: Int, vary :: Int, flag :: DoorState }

-- State monad with implcit program counter.
newtype PlusCal XState a

-- State machine functions. We need to build a stack. It will be of finite depth. This is goofy.
-- I suppose you could also use liquid haskell to prove properties of these state machines

-- internally, you'd need to write everything more dsl-like in order to introspect it much.


-}