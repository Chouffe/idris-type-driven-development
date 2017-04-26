module Label

labelFrom : Integer -> List a -> List (Integer, a)
labelFrom _ [] = []
labelFrom x (y :: xs) = (x, y) :: labelFrom (x + 1) xs

label : List a -> List (Integer, a)
label = labelFrom 0
