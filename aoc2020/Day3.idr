
module Day3 

import Data.List
import Data.Nat
import Data.Strings
import System.File

toMatrix : String -> List (List Char)
toMatrix str = map unpack (lines str)

partial
unsafeIndex : Nat -> List a -> a
unsafeIndex 0 (x::_)  = x
unsafeIndex (S k) (_::xs) = unsafeIndex k xs

partial
processLine : (Nat, Nat) -> List Char -> (Nat, Nat)
processLine (col, count) line 
  = ((col + 3) `mod` (length line), count + if unsafeIndex col line == '#' then 1 else 0)

partial
processLines : List (List Char) -> Nat
processLines = snd . foldl processLine (0, 0)

export
partial
day3 : IO ()
day3 = do
  (Right text) <- readFile "data/input3.txt" 
                      | (Left err) => printLn "Error reading file"
  printLn $ "Part1: " ++ (show $ processLines $ toMatrix text) 

