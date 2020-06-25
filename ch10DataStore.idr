module ch10DataStore
import Data.Vect 

infixr 5 .+.

public export
data Schema = SString
            | SInt
            | SChar
            | (.+.) Schema Schema 

public export
SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType SChar = Char
SchemaType (l .+. r) = (SchemaType l, SchemaType r)

export
record DataStore (schema : Schema) where
       constructor MkData
       size : Nat
       items : Vect size (SchemaType schema)

export
empty : DataStore schema
empty = MkData 0 []

export
addToStore : (newItem : SchemaType (schema)) ->
             (store : DataStore schema) ->
             DataStore schema
addToStore newItem (MkData _ items) = MkData _ (newItem :: items)

public export
data StoreView : DataStore schema -> Type where
  SNil : StoreView empty
  SAdd : (rec : StoreView store) -> StoreView (addToStore value store)

storeViewHelp : (items : Vect size (SchemaType schema) ) -> 
                StoreView (MkData size items)
storeViewHelp [] = SNil
storeViewHelp (x :: xs) = SAdd (storeViewHelp xs)

export 
storeView : (store : DataStore schema) -> StoreView store
storeView (MkData size items) = storeViewHelp items
