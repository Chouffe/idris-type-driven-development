module MergeSortView

import Data.List.Views

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
