module DataStore

import Data.Vect

-- data DataStore : Type where
--      MKData : (size : Nat) ->
--               (items : Vect size String) ->
--               DataStore

infixr 5 .+.
data Schema = SString
            | SInt
            | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

-- Record syntax: declares fields that generate automatically projection functions with the same name
record DataStore where
  constructor MkData
  schema : Schema
  size : Nat
  items : Vect size (SchemaType schema)

testDataStore : DataStore
testDataStore = MkData (SString .+. SInt) 2 [("Hello", 42), ("World", 7)]

addToStore : (store : DataStore) -> SchemaType (schema store) -> DataStore
addToStore (MkData schema size items) item = MkData schema _ (addToData items)
  where
       addToData : Vect oldsize (SchemaType schema) -> Vect (S oldsize) (SchemaType schema)
       addToData [] = [item]
       addToData (x :: xs) = x :: addToData xs


data Command : Schema -> Type where
 Add : SchemaType schema -> Command schema
 Get : Integer -> Command schema
 GetAll : Command schema
 Quit : Command schema
 Search : String -> Command schema
 SetSchema : (newSchema : Schema) -> Command schema
 Size : Command schema

parsePrefix : (schema : Schema) -> (input : String) -> Maybe (SchemaType schema, String)
parsePrefix SString input = getQuoted (unpack input)
  where
    getQuoted : List Char -> Maybe (String, String)
    getQuoted ('"' :: xs) = case span (/= '"') xs of
                                 (quoted, '"' :: rest) => Just (pack quoted, ltrim (pack rest))
                                 _ => Nothing
    getQuoted _ = Nothing

parsePrefix SInt input =
  case span isDigit input of
       ("", rest) => Nothing
       (n, rest) => Just (cast n, ltrim rest)
parsePrefix (x .+. y) input = do
  (l_val, input')  <- parsePrefix x input
  (r_val, input'') <- parsePrefix y input'
  pure ((l_val, r_val), input'')

parseBySchema : (schema : Schema) -> (input : String) -> Maybe (SchemaType schema)
parseBySchema schema input = case parsePrefix schema input of
                                  Just (res, "") => Just res
                                  Just _ => Nothing
                                  Nothing => Nothing

parseSchema : List String -> Maybe Schema
parseSchema ("String" :: xs) =
  case xs of
       [] => Just SString
       _ => case parseSchema xs of
                 Nothing => Nothing
                 Just xs_sch => Just $ SString .+. xs_sch
parseSchema ("Int" :: xs) =
  case xs of
       [] => Just SInt
       _ => case parseSchema xs of
                 Nothing => Nothing
                 Just xs_sch => Just $ SInt .+. xs_sch
parseSchema _ = Nothing

parseCommand : (schema : Schema) ->
               (cmd : String) ->
               (args : String) ->
               Maybe (Command schema)
parseCommand schema "add" str = case (parseBySchema schema str) of
                                     Nothing => Nothing
                                     Just restok => Just $ Add restok
parseCommand schema "get" "" = Just GetAll
parseCommand schema "get" val = case all isDigit (unpack val) of
                                     False => Nothing
                                     True => Just $ Get (cast val)
parseCommand schema "quit" "" = Just Quit
parseCommand schema "size" "" = Just Size
parseCommand schema "search" str = Just $ Search str
parseCommand schema "schema" str = case parseSchema (words str) of
                                        Nothing => Nothing
                                        Just schema => Just $ SetSchema schema
parseCommand schema _ _ = Nothing

parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = case Strings.span (/= ' ') input of
                          (cmd, args) => parseCommand schema cmd (ltrim args)

display : SchemaType schema -> String
display {schema = SString} item = item
display {schema = SInt} item = show item
display {schema = (x .+. y)} (iteml, itemr) = display iteml ++ "," ++ display itemr


getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store = let storeItems = items store in
                         case integerToFin pos (size store) of
                              Nothing => Just ("Out of range\n", store)
                              Just idx => Just (display (index idx storeItems) ++ "\n", store)

getAllEntries : (store : DataStore) -> Maybe (String, DataStore)
getAllEntries store = case size store of
                           Z => Just ("Nothing to display\n", store)
                           _ => let optAllEntries = sequence $ map (map fst . (flip getEntry store)) [0 .. (cast (size store) - 1)] in  -- How to do a type safe map?
                                    case optAllEntries of
                                         Nothing => Nothing
                                         Just allEntries => Just (unlines allEntries, store)

-- searchEntry : (str : String) -> (store : DataStore) -> Maybe (String, DataStore)
-- searchEntry str store = let results = Foldable.concat $ Functor.map (\it => it ++ "\n") $ Data.Vect.filter (Strings.isInfixOf str) (items store) in
--                             Just (results, store)

setSchema : (store : DataStore) -> (schema : Schema) -> Maybe DataStore
setSchema store schema = case size store of
                              Z => Just (MkData schema _ [])
                              (S k) => Nothing

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input = case parse (schema store) input of
                                 Nothing => Just ("Invalid command\n", store)
                                 Just (Add item) => Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
                                 Just (Get x) => getEntry x store
                                 Just GetAll => getAllEntries store
                                 Just Size => Just ("Store Size: " ++ show (size store) ++ "\n", store)
                                 -- Just (Search str) => searchEntry str store
                                 Just (SetSchema newSchema) => case setSchema store newSchema of
                                                                    Nothing => Just ("Can't update schema\n", store)
                                                                    Just newStore => Just ("Schema set!", newStore)
                                 Just Quit => Nothing

main : IO ()
main = replWith (MkData (SString .+. SInt) _ []) "Command: " processInput

-- Example of replWith onInput function
sumInputs : Integer -> String -> Maybe (String, Integer)
sumInputs state input =
  let val = cast input in
      if val < 0
         then Nothing
         else let newVal = state + val in
                  Just ("Subtotal: " ++ show newVal ++ "\n", newVal)
