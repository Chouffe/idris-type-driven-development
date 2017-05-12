module WordCount

import ProcessLib

record WCData where
  constructor MkWCData
  wordCount : Nat
  lineCount : Nat

doCount : (content : String) -> WCData
doCount content = MkWCData (length (words content)) (length (lines content))

data WC = CountFile String | GetData String

WCType : WC -> Type
WCType (CountFile _) = ()
WCType (GetData _) = Maybe WCData

countFile : List (String, WCData) -> String -> Process WCType (List (String, WCData)) Sent Sent
countFile files fname = do
  Right content <- Action $ readfile fname | Left err => Pure files
  let count = doCount content
  Action $ putStrLn $ "Counting complete for " ++ fname
  Pure ((fname, count) :: files)

wcService : (loaded : List (String, WCData)) -> Service WCType () -- Loops indefinitely and takes a list of loaded files as an argument
wcService loaded = do msg <- Response (\msg => case msg of
                                                    CountFile fname => Pure ()
                                                    GetData fname => Pure $ lookup fname loaded)
                      newLoaded <- case msg of
                                        Just (CountFile fname) => countFile loaded fname
                                        _ => Pure loaded
                      Loop (wcService newLoaded)

procMain : Client ()
procMain = do Just wc <- Spawn (wcService []) | Nothing => Action $ putStrLn "Spawned failed"
              Action $ putStrLn "Counting test.txt"
              Request wc (CountFile "test.txt")

              Action $ putStrLn "Processing"
              Just wcdata <- Request wc (GetData "test.txt") | Nothing => Action $ putStrLn "File Error"
              Action $ putStrLn $ "Words: " ++ show (wordCount wcdata)
              Action $ putStrLn $ "Lines: " ++ show (lineCount wcdata)

-- With process we have defined a type that allows to describe concurrently executing processes following a protocol
-- + A service must respond to every messages it receives, on a specified interfacem and continue responding in a loop
-- + A client can send message to a process, with the corresponding interface and be sure of receiving a reply of the correct type
