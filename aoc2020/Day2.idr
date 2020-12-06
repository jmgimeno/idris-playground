
module Day2

import Data.List
import Data.Nat
import Data.String.Parser
import Data.Strings
import System.File

record LineData where
  constructor MkLineData
  min, max: Nat 
  target: Char
  text: List Char

line : Parser LineData
line = do
  min <- natural
  char '-'
  max <- natural
  space
  target <- letter
  char ':'
  space
  text <- many letter
  pure $ MkLineData min max target text

parse : String -> Maybe LineData
parse s = case runIdentity $ runParser line (S s 0 (cast (length s))) of
               OK ld _ => Just ld
               _       => Nothing

countIf : (a -> Bool) -> List a -> Nat
countIf f [] = 0
countIf f (x::xs) = if f x then 1 + countIf f xs else countIf f xs

checkLines : (LineData -> Bool) -> List String -> Maybe Nat
checkLines check l = map (countIf check) $ traverse parse l

partial
unsafeIndex : Eq a => Int -> List a -> a
unsafeIndex 0 (x::_)  = x
unsafeIndex n (_::xs) = unsafeIndex (n-1) xs

checkLinePart1 : LineData -> Bool
checkLinePart1 (MkLineData min max target text) 
  = let c = countIf (== target) text in
      min <= c && c <= max

partial
checkLinePart2 : LineData -> Bool
checkLinePart2 (MkLineData min max target text) 
  = let cs = [unsafeIndex (cast min-1) text, unsafeIndex (cast max-1) text] in
      countIf (== target) cs == 1
                                                             
checkLinesPart1 : List String -> Maybe Nat
checkLinesPart1 = checkLines checkLinePart1

partial
checkLinesPart2 : List String -> Maybe Nat
checkLinesPart2 = checkLines checkLinePart2

export
partial
day2 : IO ()
day2 = do
  (Right text) <- readFile "data/input2.txt" 
                      | (Left err) => printLn "Error reading file"
  (Just counter1) <- pure $ checkLinesPart1 $ lines text
                      | Nothing => printLn "A lines does not parse"  
  printLn $ "Part1: " ++ (show counter1) 
  (Just counter2) <- pure $ checkLinesPart2 $ lines text
                      | Nothing => printLn "A lines does not parse"  
  printLn $ "Part2: " ++ (show counter2) 

