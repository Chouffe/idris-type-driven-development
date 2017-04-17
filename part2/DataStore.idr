module DataStore

import Data.Vect

data DataStore : Type where
     MKData : (size : Nat) ->
              (items : Vect size String) ->
              DataStore

size : DataStore -> Nat
size (MKData size _) = size

items : (store : DataStore) -> Vect (size store) String
items (MKData _ items) = items

addToStore : DataStore -> String -> DataStore
addToStore (MKData size items) item = MKData _  (addToData items)
  where
       addToData : Vect old String -> Vect (S old) String
       addToData [] = [item]
       addToData (x :: xs) = x :: addToData xs

data Command = Add String
             | Get Integer
             | Size
             | Search String  -- TODO
             | Quit

parseCommand : (cmd : String) ->
               (args : String) ->
               Maybe Command
parseCommand "add" str = Just $ Add str
parseCommand "get" val = case all isDigit (unpack val) of
                              False => Nothing
                              True => Just $ Get (cast val)
parseCommand "quit" "" = Just Quit
parseCommand "size" "" = Just Size
parseCommand "search" str = Just $ Search str
parseCommand _ _ = Nothing

parse : (input : String) -> Maybe Command
parse input = case Strings.span (/= ' ') input of
                   (cmd, args) => parseCommand cmd (ltrim args)


getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store = let storeItems = items store in
                         case integerToFin pos (size store) of
                              Nothing => Just ("Out of range\n", store)
                              Just idx => Just (index idx storeItems ++ "\n", store)

searchEntry : (str : String) ->
              (store : DataStore) ->
              Maybe (String, DataStore)
searchEntry str store = let results = Foldable.concat $ Functor.map (\it => it ++ "\n") $ Data.Vect.filter (Strings.isInfixOf str) (items store) in
                            Just (results, store)

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input = case parse input of
                                 Nothing => Just ("Invalid command\n", store)
                                 Just (Add item) => Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
                                 Just (Get x) => getEntry x store
                                 Just Size => Just ("Store Size: " ++ show (size store) ++ "\n", store)
                                 Just (Search str) => searchEntry str store
                                 Just Quit => Nothing

main : IO ()
main = replWith (MKData _ []) "Command: " processInput

-- Example of replWith onInput function
sumInputs : Integer -> String -> Maybe (String, Integer)
sumInputs state input =
  let val = cast input in
      if val < 0
         then Nothing
         else let newVal = state + val in
                  Just ("Subtotal: " ++ show newVal ++ "\n", newVal)
