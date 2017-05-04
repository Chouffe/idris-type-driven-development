module TreeStateLable

import Control.Monad.State

data Tree a = Empty
            | Node (Tree a) a (Tree a)

testTree : Tree String
testTree = Node (Node (Node Empty "Jim" Empty) "Fred"
                      (Node Empty "Sheila" Empty)) "Alice"
                (Node Empty "Bob" (Node Empty "Eve" Empty))

flatten : Tree a -> List a
flatten Empty = []
flatten (Node left val right) = flatten left ++ val :: flatten right

treeLabelWith : Tree a -> State (Stream labelType) (Tree (labelType, a))
treeLabelWith Empty = pure Empty
treeLabelWith (Node left val right) = do
  leftLabelled <- treeLabelWith left
  (this :: rest) <- get
  put rest
  rightLabelled <- treeLabelWith right
  pure $ Node leftLabelled (this, val) rightLabelled

treeLabel : Tree a -> Tree (Integer, a)
treeLabel tree = evalState (treeLabelWith tree) [1..]

update : (stateType -> stateType) -> State stateType ()
update f = do
  st <- get
  put $ f st

countEmpty : Tree a -> State Nat ()
countEmpty Empty = update (+1)
countEmpty (Node left _ right) = do
  countEmpty left
  n1 <- get
  put Z
  countEmpty right
  n2 <- get
  put (n1 + n2)

-- execState (countEmpty testTree) 0

countEmptyNode : Tree a -> State (Nat, Nat) ()
countEmptyNode Empty = update (\(x, y) => (1 + x, y))  -- Use Lenses?
countEmptyNode (Node left _ right) = do
  countEmptyNode left
  (n1, m1) <- get
  put (cast 0, cast 1)
  countEmptyNode right
  (n2, m2) <- get
  put (n1 + n2, m1 + m2)

-- execState (countEmptyNode testTree) (0, 0)
