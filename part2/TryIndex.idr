module TryIndex

import Data.Vect

tryIndex : Integer -> Vect n a -> Maybe a
-- tryIndex _ [] = Nothing
-- tryIndex 0 (y :: _) = Just y
-- tryIndex x (_ :: ys) = tryIndex (x - 1) ys
tryIndex {n} i xs = case integerToFin i n of
                         Nothing => Nothing
                         (Just idx) => Just (Data.Vect.index idx xs)
