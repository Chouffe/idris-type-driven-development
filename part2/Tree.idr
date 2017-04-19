module Tree

data Tree elem = Empty
               | Node (Tree elem) elem (Tree elem)

Eq elem => Eq (Tree elem) where
  (==) Empty Empty = True
  (==) (Node left val right) (Node left' val' right') = left == left' && val == val' && right == right'
  (==) _ _ = False

Foldable Tree where
  foldr f init Empty = init
  foldr f init (Node left val right) =
    let rightFold = foldr f init right
        leftFold = foldr f rightFold left
    in f val leftFold
