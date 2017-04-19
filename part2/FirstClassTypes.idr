module FirstClassTypes

import Data.Vect

-- Type synonyms
Position : Type
Position = (Double, Double)

Polygon : Nat -> Type
Polygon n = Vect n Position

tri : Polygon 3
tri = [(0.0, 0.0), (3.0, 0.0), (0.0, 4.0)]

square : Polygon 4
square = [
 (?square_rhs1, ?square_rhs2),
 (?square_rhs3, ?square_rhs4),
 (?square_rhs5, ?square_rhs6),
 (?square_rhs7, ?square_rhs8)]

StringOrInt : Bool -> Type
StringOrInt False = String
StringOrInt True = Int

getStringOrInt : (isInt : Bool) -> StringOrInt isInt
getStringOrInt False = "Ninety four"
getStringOrInt True = 94

valToString : (isInt : Bool) -> StringOrInt isInt -> String
valToString False x = trim x
valToString True integer = cast integer

valToString' : (isInt : Bool) ->
               (case isInt of
                     False => String
                     True => Int) ->
               String
valToString' False x = trim x
valToString' True x = cast x

-- Type level functions exist at compile time only
-- No runtime representation of Type
-- No pattern matching on Type directly
-- Only functions that are total will be evaluated at the type level => To terminate type inference

AdderType : (numargs : Nat) -> Type -> Type
AdderType Z numType = numType
AdderType (S k) numType = (next : numType) -> AdderType k numType

adder : Num numType => (k: Nat) -> numType -> AdderType k numType
adder Z acc = acc
adder (S k) acc = \next => adder k (next + acc)

-- Printf function
-- printf "Hello!" : String
-- printf "Answer: %d" : Int -> String
-- printf "%s number %d" : String -> Int -> String

data Format = Number Format      -- %d followed by the rest
            | Str Format         -- %s followed by the rest
            | Ch Format          -- %c followed by the rest
            | Do Format          -- %f followed by the rest
            | Lit String Format  -- Literal String followed by the rest
            | End                -- Empty format specifier

-- Eg: "%s = %d" -> Str (Lit " = " (Number End))
-- Defining an intermediate data type to separate parsing from evaluation

PrintfType : Format -> Type
PrintfType (Number fmt) = (i : Int) -> PrintfType fmt
PrintfType (Ch fmt) = (c : Char) -> PrintfType fmt
PrintfType (Do fmt) = (f : Double) -> PrintfType fmt
PrintfType (Str fmt) = (str: String) -> PrintfType fmt
PrintfType (Lit str fmt) = PrintfType fmt
PrintfType End = String

printfFmt : (fmt : Format) -> (acc : String) -> PrintfType fmt
printfFmt (Number fmt) acc = \i => printfFmt fmt (acc ++ show i)
printfFmt (Str fmt) acc = \str => printfFmt fmt (acc ++ str)
printfFmt (Ch fmt) acc = \c => printfFmt fmt (acc ++ show c)
printfFmt (Do fmt) acc = \d => printfFmt fmt (acc ++ show d)
printfFmt (Lit lit fmt) acc = printfFmt fmt (acc ++ lit)
printfFmt End acc = acc

toFormat : (xs : List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: chars) = Number (toFormat chars)
toFormat ('%' :: 's' :: chars) = Str (toFormat chars)
toFormat ('%' :: 'c' :: chars) = Ch (toFormat chars)
toFormat ('%' :: 'f' :: chars) = Do (toFormat chars)
toFormat ('%' :: chars) = Lit "%" (toFormat chars)
toFormat (c :: chars) = case toFormat chars of
                             Lit lit chars' => Lit (strCons c lit) chars'
                             fmt => Lit (strCons c "") fmt

printf : (fmt : String) -> PrintfType (toFormat (unpack fmt))
printf fmt = printfFmt _ ""

-- Exercises
Matrix : Nat -> Nat -> Type
Matrix n m = Vect n (Vect m Double)

TupleVect : (k : Nat) -> Type -> Type
TupleVect Z _ = ()
TupleVect (S k) type = (type, TupleVect k type)

test : TupleVect 4 Nat
test = (0, 0, 0, 0, ())
