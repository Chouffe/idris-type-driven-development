module DataStoreRevisited

import Data.Vect

infixr 5 .+.

public export
data Schema = SString | SInt | (.+.) Schema Schema

public export
SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

-- Don't intend to allow the schema to be updated
export
record DataStore (schema : Schema) where
  constructor MkData
  size : Nat
  items : Vect size (SchemaType schema)

export
empty : DataStore schema
empty = MkData 0 []

export
addToStore : (value : SchemaType schema) -> (store : DataStore schema) -> DataStore schema
addToStore value (MkData _ items) = MkData _ (value :: items)

-- When matching on a store we'd like the following:
-- an empty case that matches a store with no contents
-- an `addToStore value store` case that matches a store where the first entry is given by value and the remaining items in the store are given by store

public export
data StoreView : DataStore schema -> Type where
  SNil : StoreView empty
  SAdd : (rec : StoreView store) -> StoreView (addToStore value store)

storeViewHelp : (items : Vect size (SchemaType schema)) -> StoreView (MkData size items)
storeViewHelp [] = SNil
storeViewHelp (val :: xs) = SAdd (storeViewHelp xs)

-- Exporting a view that allows you to traverse the content of a store by seeing how the store was constructed (either with empty or addToStore)
export
storeView : (store : DataStore schema) -> StoreView store
storeView (MkData size items) = storeViewHelp items
