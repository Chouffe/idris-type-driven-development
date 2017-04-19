module Eq

occurrences : Eq ty => (item : ty) -> (values : List ty) -> Nat
occurrences item =  length . filter (== item)

data Matter = Solid | Liquid | Gas

-- Implementation of Eq for Matter
Eq Matter where
  (==) Solid Solid = True
  (==) Liquid Liquid = True
  (==) Gas Gas = True
  (==) _ _ = False

data Tree elem = Empty
               | Node (Tree elem) elem (Tree elem)

Eq elem => Eq (Tree elem) where
  (==) Empty Empty = True
  (==) (Node left val right) (Node left' val' right') = left == left' && val == val' && right == right'
  (==) _ _ = False
