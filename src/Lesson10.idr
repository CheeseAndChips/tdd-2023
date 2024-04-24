module Lesson10

import Data.Vect

%default total

infixr 5 .+.

public export 
data Schema = SString
            | SInt
            | (.+.) Schema Schema

public export
SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

-- record DataStore' (t: Type) where

export
record DataStore (schema : Schema) where
  constructor MkData
  size : Nat
  items : Vect size (SchemaType schema)

export
emp : DataStore schema
emp = (MkData 0 [])

export
addToStore : (value : SchemaType schema) -> 
             (store : DataStore schema) ->
             DataStore schema
addToStore value (MkData _ items) = MkData _ (value :: items)

testStore : DataStore (SString .+. SString .+. SInt)
testStore = addToStore ("Mercury", "Mariner 10", 1974) $ 
            addToStore ("Venus", "Venera", 1961) $
            emp

public export
data StoreView : (schema : _) -> DataStore schema -> Type where
  SNil : StoreView schema emp
  SAdd : (value, store: _) -> (rec : StoreView schema store) ->
         StoreView schema ((addToStore value store))

storeViewHelp : {size : _} -> 
               (items : Vect size ((SchemaType schema))) ->
                StoreView schema (MkData size items)
storeViewHelp [] = SNil
storeViewHelp (x :: xs) = SAdd x _ (storeViewHelp xs)

storeView : (store : DataStore schema) -> StoreView schema store
storeView (MkData size items) = storeViewHelp items

listItems : DataStore schema -> List (SchemaType schema)
listItems x with (storeView x)
  listItems x | SNil = []
  listItems (addToStore value store) | (SAdd value store rec) =
    value :: listItems store | rec


