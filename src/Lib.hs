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
  