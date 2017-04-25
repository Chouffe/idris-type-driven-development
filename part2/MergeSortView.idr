module MergeSortView

import Data.List.Views
import Data.Vect
import Data.Vect.Views
import Data.Nat.Views

total
mergeSort : Ord a => List a -> List a
mergeSort xs with (splitRec xs)
  mergeSort [] | SplitRecNil = []
  mergeSort [x] | SplitRecOne = [x]
  mergeSort (lefts ++ rights) | (SplitRecPair lrec rrec) = merge (mergeSort lefts | lrec) (mergeSort rights | rrec)

-- Exercises
equalSuffix : Eq a => List a -> List a -> Bool
equalSuffix xs ys with (snocList xs)
  equalSuffix [] ys | Empty = True
  equalSuffix (zs ++ [x]) ys | (Snoc xsrec) with (snocList ys)
    equalSuffix (zs ++ [x]) [] | (Snoc xsrec) | Empty = False
    equalSuffix (zs ++ [x]) (vs ++ [y]) | (Snoc xsrec) | (Snoc ysrec) =
      x == y && equalSuffix zs vs | xsrec | ysrec

commonSuffix : Eq a => List a -> List a -> List a
commonSuffix xs ys with (snocList xs)
  commonSuffix [] ys | Empty = []
  commonSuffix (zs ++ [x]) ys | (Snoc xsrec) with (snocList ys)
    commonSuffix (zs ++ [x]) [] | (Snoc xsrec) | Empty = []
    commonSuffix (zs ++ [z]) (vs ++ [v]) | (Snoc xsrec) | (Snoc ysrec) =
      case z == v of
           False => []
           True => (commonSuffix zs vs | xsrec | ysrec) ++ [z]

mergeSortVect : Ord a => Vect n a -> Vect n a
mergeSortVect xs with (Data.Vect.Views.splitRec xs)
  mergeSortVect [] | SplitRecNil = []
  mergeSortVect [x] | SplitRecOne = [x]
  mergeSortVect (ys ++ zs) | (SplitRecPair lrec rrec) = merge (mergeSortVect ys | lrec) (mergeSortVect zs | rrec)

total
toBinary : Nat -> String
toBinary (S Z) = "1"
toBinary k with (halfRec k)
  toBinary Z | HalfRecZ = "0"
  toBinary (n + n) | (HalfRecEven rec) = toBinary n | rec ++ "0"
  toBinary (S (n + n)) | (HalfRecOdd rec) = toBinary n | rec ++ "1"

total
palindrome : Eq a => List a -> Bool
palindrome xs with (vList xs)
  palindrome [] | VNil = True
  palindrome [x] | VOne = True
  palindrome (x :: (ys ++ [y])) | (VCons rec) = x == y && palindrome ys | rec
-- The VList view allows to traverse a list in linear time, processing the first and last elements simultaneously and recursing on the middle of the list
