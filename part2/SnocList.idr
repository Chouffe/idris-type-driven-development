module SnocList

data SnocList : List a -> Type where
  Empty : SnocList []
  Snoc : (rec : SnocList xs) -> SnocList (xs ++ [x])

snocListHelp : (snoc : SnocList ys) ->
               (rest : List a) ->
               SnocList (ys ++ rest)
snocListHelp {ys} snoc [] = rewrite appendNilRightNeutral ys in snoc
snocListHelp {ys} snoc (x :: xs) = rewrite appendAssociative ys [x] xs in
                                           snocListHelp (Snoc snoc {x}) xs

snocList : (xs : List a) ->  SnocList xs
snocList xs = snocListHelp Empty xs

total
myReverseHelper : (xs : List a) -> SnocList xs -> List a
myReverseHelper [] Empty = []
myReverseHelper (ys ++ [x]) (Snoc rec) = x :: myReverseHelper ys rec

total
myReverse : List a -> List a
myReverse xs = myReverseHelper xs (snocList xs)

-- Still same problem as before: rebuilds the view using snocList xs
-- not total
myReverse2 : List a -> List a
myReverse2 xs with (snocList xs)
  myReverse2 [] | Empty = []
  myReverse2 (ys ++ [x]) | (Snoc rec) = x :: myReverse2 ys

-- Here is the solution: it bypasses the construction snocList input and uses rec directly
-- myReverse3 runs in linear time :)
myReverse3 : List a -> List a
myReverse3 xs with (snocList xs)
  myReverse3 [] | Empty = []
  myReverse3 (xs ++ [x]) | (Snoc rec) = x :: myReverse3 xs | rec

total
isSuffix : Eq a => List a -> List a -> Bool
isSuffix xs ys with (snocList xs)
  isSuffix [] ys | Empty = True
  isSuffix (zs ++ [x]) ys | (Snoc xsrec) with (snocList ys)
    isSuffix (zs ++ [x]) [] | (Snoc xsrec) | Empty = False
    isSuffix (zs ++ [x]) (vs ++ [y]) | (Snoc xsrec) | (Snoc ysrec) =
      x == y && isSuffix zs vs | xsrec | ysrec
