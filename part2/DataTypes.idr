module DataTypes

data Bool = False | True

data Direction = North | East | South | West

turnClockwise : Direction -> Direction
turnClockwise North = East
turnClockwise East = South
turnClockwise South = West
turnClockwise West = North

data Shape = ||| A triangle, with its base length and height
             Triangle Double Double
           | ||| A rectangle, with its length and height
           Rectangle Double Double
           | ||| A circle, with its radius
           Circle Double

-- GADT like syntax: more general and flexible
data Shape2 : Type where
     Triangle2 : (base : Double) -> (height : Double) -> Shape2
     Rectangle2 : (length : Double) -> (heigth : Double) -> Shape2
     Circle2 : (radius : Double) -> Shape2

area : Shape -> Double
area (Triangle base height) = base * height * 0.5
area (Rectangle length height) = length * height
area (Circle radius) = pi * radius * radius

-- Recursive types
data Nat' = Z' | S' Nat'

data Picture = Primitive Shape
             | Combine Picture Picture
             | Rotate Double Picture
             | Translate Double Double Picture

rectangle : Picture
rectangle = Primitive $ Rectangle 20 10

circle : Picture
circle = Primitive $ Circle 5

triangle : Picture
triangle = Primitive $ Triangle 10 10

testPicture : Picture
testPicture = Combine (Translate 5 5 rectangle)
              (Combine (Translate 35 5 circle)
              (Translate 15 25 triangle))

%name Shape shape, shape1, shape2
%name Picture pic, pic1, pic2
pictureArea : Picture -> Double
pictureArea (Primitive shape) = area shape
pictureArea (Combine pic pic1) = pictureArea pic + pictureArea pic1
pictureArea (Rotate _ pic) = pictureArea pic
pictureArea (Translate _ _ pic) = pictureArea pic

-- Generic Data Types
-- data Maybe a = Nothing | Just a

data Either a b = Left a | Right b

-- data Tree a = Empty
--             | Node (Tree a) a (Tree a)
-- %name Tree tree, tree1

-- insert : Ord a => a -> Tree a -> Tree a
-- insert x Empty = Node Empty x Empty
-- insert x orig@(Node left val right) = case compare x val of
--                                            LT => Node (insert x left) val right
--                                            EQ => orig
--                                            GT => Node left val (insert x right)

data BSTree : Type -> Type where
     Empty : Ord elem =>
             BSTree elem
     Node : Ord elem =>
            (left : BSTree elem) ->
            (val : elem) ->
            (right : BSTree elem) ->
            BSTree elem
%name BSTree bstree, bstree1

insert : a -> BSTree a -> BSTree a
insert x Empty = Node Empty x Empty
insert x orig@(Node left val right) = case compare x val of
                                      LT => Node (insert x left) val right
                                      EQ => orig
                                      GT => Node left val (insert x right)

listToTree : Ord elem => List elem -> BSTree elem
listToTree [] = Empty
listToTree (x :: xs) = insert x $ listToTree xs

treeToList : BSTree elem -> List elem
treeToList Empty = []
treeToList (Node left val right) = treeToList left ++ [val] ++ treeToList right

data Expr : Type where
     Val : (val : Int) -> Expr
     Add : (e1 : Expr) -> (e2 : Expr) -> Expr
     Sub : (e1 : Expr) -> (e2 : Expr) -> Expr
     Mult : (e1 : Expr) -> (e2 : Expr) -> Expr

evaluate : Expr -> Int
evaluate (Val val) = val
evaluate (Add e1 e2) = evaluate e1 + evaluate e2
evaluate (Sub e1 e2) = evaluate e1 - evaluate e2
evaluate (Mult e1 e2) = evaluate e1 * evaluate e2

-- evaluate (Mult (Val 10) (Add (Val 6) (Val 3)))
-- 90 : Int

maxMaybe : Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe mx my = do
  x <- mx
  y <- my
  return $ max x y

-- Dependent Types
data PowerSource = Petrol | Pedal | Electric

data Vehicle : PowerSource -> Type where
     Bicycle : Vehicle Pedal
     Unicycle : Vehicle Pedal

     Tram : Vehicle Electric

     Motorcycle : (fuel : Nat) -> Vehicle Petrol
     Car : (fuel : Nat) -> Vehicle Petrol
     Bus : (fuel : Nat) -> Vehicle Petrol

wheels : Vehicle _ -> Nat
wheels Tram = 20
wheels Bicycle = 2
wheels Unicycle = 1
wheels (Motorcycle _) = 2
wheels (Car _) = 4
wheels (Bus _) = 4

refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Motorcycle _) = Motorcycle 50
refuel (Car _) = Car 100
refuel (Bus _) = Bus 200
-- Optional
refuel Tram impossible
refuel Bicycle impossible
refuel Unicycle impossible

-- x : Vehicle Petrol
-- x = refuel (Car 100)
