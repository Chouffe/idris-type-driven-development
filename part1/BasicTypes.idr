module BasicTypes

average : (str : String) -> Double
average str =
  let numWords = wordCount str
      totalLength = sum (allLengths (words str))
  in cast totalLength / cast numWords
  where
    wordCount : String -> Nat
    wordCount str = length (words str)

    allLengths : List String -> List Nat
    allLengths strs = map length strs

showAverage : String -> String
showAverage str = "The average word length is: " ++ show (average str) ++ "\n"

main : IO ()
main = repl "Enter a string: " showAverage

add : Int -> Int -> Int
add x y = x + y

doubleNat : Nat -> Nat
doubleNat x = x + x

doubleInt : Int -> Int
doubleInt x = x + x

double : Num ty => ty -> ty
double ty = ty + ty

twice : (a -> a) -> a -> a
twice f x = f $ f x

-- Type declarations without definitions
Shape : Type
rotate : Shape -> Shape

turn_around : Shape -> Shape
turn_around = twice rotate

-- Anonymous functions
r0 : Nat
r0 = twice (\x => x * x) 2

-- Local binding: Let and Where
pythagoras : Double -> Double -> Double
pythagoras x y = sqrt (square x + square y)
  where
    square : Double -> Double
    square x = x * x

-- Exercises
palindrome : Nat -> String -> Bool
palindrome n str =
  if length str >= n
     then True
     else reverse lStr == lStr
  where
    lStr : String
    lStr = toLower str

count : String -> (Nat, Nat)
count str = (length (words str), length str)

top_ten : Ord a => List a -> List a
top_ten = take 10 . sort

over_length : Nat -> List String -> Nat
over_length n = length . filter (\s => length s > n)

palindromeCheck : IO ()
palindromeCheck = repl "String> " ((++ "\n") . show . palindrome 10)
