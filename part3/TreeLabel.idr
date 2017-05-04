data Tree a = Empty
            | Node (Tree a) a (Tree a)

testTree : Tree String
testTree = Node (Node (Node Empty "Jim" Empty) "Fred"
                      (Node Empty "Sheila" Empty)) "Alice"
                (Node Empty "Bob" (Node Empty "Eve" Empty))

flatten : Tree a -> List a
flatten Empty = []
flatten (Node left val right) = flatten left ++ val :: flatten right

-- Returns the unused portion of the stream as well as the labelled tree
treeLabelWith : Stream labelType -> Tree a -> (Stream labelType, Tree (labelType, a))
treeLabelWith xs Empty = (xs, Empty)
treeLabelWith xs (Node left val right) =
            let (lblThis :: lblsLeft, leftLabelled) = treeLabelWith xs left  -- Label the left subtree, which gives a new subtree and a new stream, use the first label for val
                (lblsRight, rightLabelled) = treeLabelWith lblsLeft right  -- label the right subtree using the stream returned after labeling the left subtree
            in
            (lblsRight, Node leftLabelled (lblThis, val) rightLabelled)  -- Returns the stream given by labeling the right subtree and a labeled node

-- Essentially, the function uses local mutable state by returning new state
-- It's hard to read because the details of the algo and the details of state management are complected
-- It's error prone because you need to propagate the correct state to recursive calls

treeLabel : Tree a -> Tree (Integer, a)
treeLabel tree = snd (treeLabelWith [1..] tree)

State : (stateType : Type) -> (ty : Type) -> Type
runState : State stateType a -> stateType -> (a, stateType)

get : State stateType stateType
put : stateType -> State stateType ()

(>>=) : State stateType a -> (a -> State stateType b) -> State stateType b
