module TreeLabelType

data State : (stateType : Type) -> Type -> Type where
  Get : State stateType stateType
  Put : stateType -> State stateType ()

  Pure : ty -> State stateType ty
  Bind : State stateType a -> (a -> State stateType b) -> State stateType b

(>>=) : State stateType a -> (a -> State stateType b) -> State stateType b
(>>=) = Bind

get : State stateType stateType
get = Get

put : stateType -> State stateType ()
put = Put

pure : ty -> State stateType ty
pure = Pure

runState : State stateType a -> (st : stateType) -> (a, stateType)
runState Get st = (st, st)
runState (Put newState) _ = ((), newState)
runState (Pure x) st = (x, st)
runState (Bind x f) st = let (val, nextState) = runState x st in
                             runState (f val) nextState

-- One could use do notation to define Functor, Applicative and Monad but we need a monad implementation to provide it.
-- One solution is to use a mutual block
Functor (State stateType) where
  map f x = Bind x (\val => Pure (f val))

Applicative (State stateType) where
  pure = Pure
  (<*>) f a = Bind f (\f' =>
              Bind a (\a' =>
              Pure (f' a')))

Monad (State stateType) where
  (>>=) = Bind

-- Tree

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
treeLabelWith Empty = Pure Empty
treeLabelWith (Node left val right) = do
  labelLeft <- treeLabelWith left
  (this :: rest) <- get
  put rest
  labelRight <- treeLabelWith right
  Pure $ Node labelLeft (this, val) labelRight

treeLabel : Tree a -> Tree (Nat, a)
treeLabel tree = fst $ runState (treeLabelWith tree) [1..]

-- Add Positives works because our State has a Monad instance

addIfPositive : Integer -> State Integer Bool
addIfPositive x = do
  when (x > 0) $ do
    current <- get
    put (current + x)
  pure (x > 0)

addPositives : List Integer -> State Integer Nat
addPositives xs = do
  added <- traverse addIfPositive xs
  pure $ length $ filter id added
