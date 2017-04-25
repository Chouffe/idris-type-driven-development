module TestStore

import DataStoreRevisited

testStore : DataStore (SString .+. SString .+. SInt)
testStore =
  addToStore ("Mercury", "Mariner 10", 1974) $
  addToStore ("Venus", "Venera" ,1961) $
  addToStore ("Uranus", "Voyager 2", 1986) $
  addToStore ("Pluto", "New Horizons", 2015) $
  empty

testStore2 : DataStore (SString .+. SInt)
testStore2 = addToStore ("First", 1) $
             addToStore ("Second", 2) $
             empty

listItems : DataStore schema -> List (SchemaType schema)
listItems x with (storeView x)
  listItems x | SNil = []
  listItems (addToStore value store) | (SAdd rec) = value :: listItems store | rec

filterKeys : (pred : SchemaType valSchema -> Bool) ->
             DataStore (SString .+. valSchema) ->
             List String
filterKeys pred x with (storeView x)
  filterKeys pred x | SNil = []
  filterKeys pred (addToStore (key, value) store) | (SAdd rec) =
    case pred value of
         False => filterKeys pred store
         True => key :: filterKeys pred store

-- For both listItems and filterKeys, we defined a function that does not know anything about the internal representation of the store

getValues : DataStore (SString .+. valSchema) -> List (SchemaType valSchema)
getValues x with (storeView x)
  getValues x | SNil = []
  getValues (addToStore (_, value) store) | (SAdd rec) = value :: getValues store
