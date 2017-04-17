module Interactive

import System
import Data.Vect

readNumber : IO (Maybe Nat)
readNumber = do
  input <- getLine
  if all isDigit (unpack input)
     then pure $ Just (cast input)
     else pure Nothing

readNumbers : IO (Maybe (Nat, Nat))
readNumbers = do
  optNum1 <- readNumber
  case optNum1 of
       Nothing => pure Nothing
       Just n1 => do
         optNum2 <- readNumber
         case optNum2 of
              Nothing => pure Nothing
              Just n2 => pure $ Just (n1, n2)

readPairs : IO (String, String)
readPairs = do
  x <- getLine
  y <- getLine
  pure (x, y)

readNumbers' : IO (Maybe (Nat, Nat))
readNumbers' = do
  Just n1 <- readNumber | Nothing => pure Nothing
  Just n2 <- readNumber | Nothing => pure Nothing
  pure $ Just (n1, n2)

countdown : (secs : Nat) -> IO ()
countdown Z = putStrLn "Lift off!"
countdown (S secs) = do
  putStrLn (show (S secs))
  usleep 1000000
  countdown secs

guess : (target : Nat) -> (guesses : Nat) -> IO ()
guess target guesses = do
  putStrLn "Guess my Number..."
  Just n <- readNumber | Nothing => do putStrLn "Bad number"
                                       guess target guesses
  case (compare n target) of
      LT => do putStrLn "Too Low..."
               guess target (plus 1 guesses)
      GT => do putStrLn "Too High..."
               guess target (plus 1 guesses)
      EQ => putStrLn $ "You Won in " ++ show guesses ++ " guesses!!"

-- Reading a vector of known length
readVectLen : (len : Nat) -> IO (Vect len String)
readVectLen Z = pure []
readVectLen (S k) = do
  x <- getLine
  xs <- readVectLen k
  pure $ x :: xs

-- Reading a vector of unknown length
data VectUnknown : Type -> Type where
  MkVect : (len : Nat) -> Vect len a -> VectUnknown a

readVect : IO (VectUnknown String)
readVect = do
  x <- getLine
  if (x == "")
     then pure (MkVect _ [])
     else do
       MkVect _ xs <- readVect
       pure $ MkVect _ (x :: xs)

printVect : Show a => VectUnknown a -> IO ()
printVect (MkVect len xs) = putStrLn $ show xs

-- This is a problem that arises every time you need to read from stdin or data from external data source
-- Idris has a generic solution: dependent pairs

-- A dependent pair is a more expressive form of tuple (product) where the type ofthe second element can be computed from the value of the first element
-- anyVect : (n : Nat ** Vect n String)
-- anyVect = (3 ** ["Rod", "Jane", "Freddy"])

readVect' : IO (len ** Vect len String)
readVect' = do
  x <- getLine
  if (x == "")
     then pure (_ ** [])
     else do
       (_ ** xs) <- readVect'
       pure (_ ** x :: xs)

main : IO ()
main = do
  target <- map (flip mod 100) time
  guess (cast target) Z

zipInputs : IO ()
zipInputs = do
  putStrLn "Enter first vector (blank line to end):"
  (len1 ** vect1) <- readVect'
  putStrLn "Enter second vector (blank line to end):"
  (len2 ** vect2) <- readVect'
  case (exactLength len1 vect2) of
       Nothing => putStrLn "Vectors are different lengths"
       Just vect2' => printLn $ zip vect1 vect2'

readToBlank : IO (List String)
readToBlank = do
  x <- getLine
  case (x == "") of
       True => pure []
       False => do
         xs <- readToBlank
         pure $ x :: xs

getFilename : IO String
getFilename = do
  putStr "Filename> "
  getLine

save : (result : String) -> IO ()
save result = do
  filename <- getFilename
  writeResult <- writeFile filename result
  either printLn (pure . id) writeResult

readAndSave : IO ()
readAndSave = readToBlank >>= save . unlines

readVectFile : (filename : String) -> IO (n ** Vect n String)
readVectFile filename = do
  Right content <- readFile filename
    | Left err => do
           putStrLn $ "Error> " ++ show err
           pure (_ ** [])
  pure (_ ** fromList (lines content))
