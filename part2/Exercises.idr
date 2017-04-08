module Exercises

import Data.Vect

-- List functions

total mlength : List a -> Nat
mlength = sum . map (const 1)

total mreverse : List a -> List a
mreverse = foldl (\acc, x => x :: acc) []

total mmap : (a -> b) -> List a -> List b
mmap _ [] = []
mmap f (x :: xs) = f x :: mmap f xs

total mmap' : (a -> b) -> Vect n a -> Vect n b
mmap' f [] = []
mmap' f (x :: xs) = f x :: mmap' f xs

-- Matrices

m1 : Vect 3 (Vect 4 Int)
m1 = [
  [1, 2, 3, 4]
, [5, 6, 7, 8]
, [9, 10, 11, 12]
]

m2 : Vect 3 (Vect 4 Int)
m2 = [
  [0, 1, 0, 1]
, [1, 0, 1, 0]
, [0, 1, 0, 1]
]

addMatrix : Num a =>
            Vect rows (Vect cols a) ->
            Vect rows (Vect cols a) ->
            Vect rows (Vect cols a)
addMatrix m1 m2 = zipWith (\r1, r2 => zipWith (+) r1 r2) m1 m2

createEmpties : Vect n (Vect 0 a)
-- createEmpties = replicate _ []
createEmpties {n = Z} = []
createEmpties {n = (S k)} = [] :: createEmpties
-- createEmpties {a=Nat} {n=10}

transposeHelper : (x: Vect n a) ->
                  (xsTrans : Vect n (Vect k a)) ->
                  Vect n (Vect (S k) a)
transposeHelper [] [] = []
transposeHelper (x :: xs) (y :: ys) = (x :: y) :: transposeHelper xs ys

transposeMatrix : Vect m (Vect n a) -> Vect n (Vect m a)
transposeMatrix [] = createEmpties
transposeMatrix (x :: xs) = let xsTrans = transposeMatrix xs in
                                -- transposeHelper x xsTrans
                                zipWith (::) x xsTrans

total multMatrixHelperRow : Num a => (row : Vect n a) -> (columns : Vect k (Vect n a)) -> Vect k a
multMatrixHelperRow row = map (\column => sum $ zipWith (*) column row)

total multMatrixHelper : Num a =>
                         (m1 : Vect n (Vect m a)) ->
                         (m2' : Vect k (Vect m a)) ->
                         Vect n (Vect k a)
multMatrixHelper [] _ = []
multMatrixHelper _ [] = replicate _ []
multMatrixHelper (row :: rows) columns = (multMatrixHelperRow row columns) :: multMatrixHelper rows columns

total multMatrix : Num a =>
                   (m1 : Vect n (Vect m a)) ->
                   (m2 : Vect m (Vect k a)) ->
                   Vect n (Vect k a)
multMatrix m1 m2 = let columns = transposeMatrix m2 in multMatrixHelper m1 columns
