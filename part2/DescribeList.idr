module DescribeList


-- ListLast dependent type that gives alternative patterns for a list
data ListLast : List a -> Type where
  Empty : ListLast []
  NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

describeHelper : (input : List Int) -> (form : ListLast input) ->  String
describeHelper [] Empty = "Empty"
describeHelper (xs ++ [x]) (NonEmpty xs x) = "Non Empty, initial portion = " ++ show xs
-- ListLast is a view because it provides an alternative means of  viewing the data
-- In practice, need to be able to convert an input list xs into a value of type ListLast xs

total
listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) = case listLast xs of
                          Empty => NonEmpty [] x
                          (NonEmpty ys y) => NonEmpty (x :: ys) y
-- listLast is the covering function of the ListLast view
-- How to convert a value into a view of that value

describeListEnd : List Int -> String
describeListEnd xs = describeHelper xs (listLast xs)

-- Dependent pattern matching is so common in Idris that there's a construct for expressing extended pattern matching: the with construct

describeListEnd2 : List Int -> String
describeListEnd2 xs with (listLast xs)
  describeListEnd2 [] | Empty = "Empty"
  describeListEnd2 (ys ++ [x]) | (NonEmpty ys x) = "Non Empty, initial portion = " ++ show ys

-- with allows matching on intermediate results and introduces a new pattern to match on the left side of the definition.

myReverse : List a -> List a
myReverse xs with (listLast xs)
  myReverse [] | Empty = []
  myReverse (ys ++ [x]) | (NonEmpty ys x) = x :: myReverse ys

-- Very inefficient because it constructs ListLast xs on every recursive call, and constructing ListLast xs requires traversing xs
-- Idris cant decide if the function is total

data SplitList : List a -> Type where
  SplitNil : SplitList []
  SplitOne : SplitList [x]
  SplitPair : (lefts : List a) -> (rights : List a) -> SplitList (lefts ++ rights)

total
splitList : (xs : List a) -> SplitList xs
splitList xs = splitListHelper xs xs
  where
    splitListHelper : List a -> (xs : List a ) -> SplitList xs
    splitListHelper _ [] = SplitNil
    splitListHelper _ [x] = SplitOne
    splitListHelper (_ :: _ :: counter) (item :: items) =
      case splitListHelper counter items of
           SplitNil => SplitOne
           SplitOne {x} => SplitPair [item] [x]
           (SplitPair lefts rights) => SplitPair (item :: lefts) rights
    splitListHelper _ items = SplitPair [] items


mergeSort : Ord a => List a -> List a
mergeSort xs with (splitList xs)
  mergeSort [] | SplitNil = []
  mergeSort [x] | SplitOne = [x]
  mergeSort (lefts ++ rights) | (SplitPair lefts rights) = merge (mergeSort lefts) (mergeSort rights)

-- Idris cant tell mergeSort is total though :((

-- TakeN view allows traversal of a list several elements at a time
data TakeN : List a -> Type where
  Fewer : TakeN xs
  Exact : (n_xs : List a) -> TakeN (n_xs ++ rest)

takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN Z [] = Exact []
takeN Z (x :: _) = Exact []
takeN (S k) [] = Fewer
takeN (S k) (x :: xs) = case takeN k xs of
                             Fewer => Fewer
                             (Exact n_xs) => Exact $ x :: n_xs

groupByN : (n : Nat) -> (xs : List a) -> List (List a)
groupByN n xs with (takeN n xs)
  groupByN n xs | Fewer = [xs]
  groupByN n (n_xs ++ rest) | (Exact n_xs) = n_xs :: groupByN n rest

halves : List a -> (List a, List a)
halves xs with (takeN (div (length xs) 2) xs)
  halves xs | Fewer = ([], xs)
  halves (n_xs ++ rest) | (Exact n_xs) = (n_xs, rest)
