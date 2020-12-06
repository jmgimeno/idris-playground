module Day1

import Data.List
import Data.Maybe
import Data.Strings
import Data.Vect
import System.File

readInts : String -> List Integer
readInts s = map toInt mints
  where 
    toInt : Maybe Integer -> Integer
    toInt = fromMaybe 0
    mints : List (Maybe Integer)
    mints = map parseInteger (words s)

combine : (n : Nat) -> List a -> List (Vect n a)
combine Z _ = [[]]
combine (S k) [] = []
combine (S k) (x :: xs) = map (x::) (combine k xs) ++ combine (S k) xs

part1 : String -> Maybe (Vect 2 Integer)
part1 = find (\xs => sum xs == 2020) . combine 2 . readInts

part2 : String -> Maybe (Vect 3 Integer)
part2 = find (\xs => sum xs == 2020) . combine 3 . readInts

export
day1 : IO ()
day1 = do
  (Right lines) <- readFile "data/input1.txt" | (Left err) => printLn "Error reading file"
  (Just xs) <- pure (part1 lines) | Nothing => printLn "Not found"
  printLn $ "Part1: " ++ show (product xs)
  (Just xs) <- pure (part2 lines) | Nothing => printLn "Not found"
  printLn $ "Part2: " ++ show (product xs)
