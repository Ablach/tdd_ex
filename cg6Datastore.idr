module Main
import Data.Vect 

infixr 5 .+.

data Schema = SString
            | SInt
            | SChar
            | (.+.) Schema Schema 

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType SChar = Char
SchemaType (l .+. r) = (SchemaType l, SchemaType r)

{-

data DataStore : Type where
     MkData : (schema : Schema) -> 
              (size : Nat) ->             
              (items : Vect size (SchemaType schema)) ->
              DataStore

schema : DataStore -> Schema                                                              
schema (MkData schema' size' items') = schema'

size : DataStore -> Nat             
size (MkData schema' size' items') = size'

items : (store : DataStore) -> Vect (size store) (SchemaType (schema store))
items (MkData schema' size' items') = items'

-}

record DataStore where
       constructor MkData
       schema : Schema
       size : Nat
       items : Vect size (SchemaType schema)


addToStore : (store : DataStore) -> SchemaType (schema store) -> DataStore
addToStore (MkData schema size items) newItem 
  = MkData schema _ (addToData items)
    where
      addToData : Vect old (SchemaType schema) -> 
                    Vect (S old) (SchemaType schema)
      addToData [] = [newItem]
      addToData (x :: xs) = x :: addToData xs


data Command : Schema -> Type where
  SetSchema : (newSchema : Schema) -> Command schema
  Add : SchemaType schema -> Command schema
  Get : Integer -> Command schema
  GetAll : Command schema
  Quit : Command schema


parsePrefix : (schema : Schema) -> (str : String) -> Maybe (SchemaType schema, String)     
parsePrefix SString str = getQuoted (unpack str)
  where
    getQuoted : List Char -> Maybe (String, String)
    getQuoted ('"' :: xs) = case span (/= '"') xs of
                              (quoted, '"' :: rest) => Just (pack quoted, ltrim (pack rest))
                              _                     => Nothing
    getQuoted _ = Nothing

parsePrefix SInt str = case span isDigit str of
                         ("", rest)  => Nothing
                         (num, rest) => Just (cast num, ltrim rest)
                         
parsePrefix SChar str = (case unpack str of
                              [] => Nothing
                              (x :: xs) => Just (x, ltrim (pack xs)))                       

parsePrefix (l .+. r) str = 
  do
     (schemal, rest) <- parsePrefix l str
     (schemar, rest') <- parsePrefix r rest           
     Just ((schemal, schemar), rest')


parseBySchema : (schema : Schema) -> (str : String) -> Maybe (SchemaType schema)
parseBySchema schema str = case parsePrefix schema str of
                             (Just (a, "")) => Just a
                             otherwise      => Nothing


parseSchema : List String -> Maybe Schema
parseSchema("String" :: xs) 
  = case xs of
      [] => Just SString
      _ => do x <-parseSchema xs 
              Just (SString .+. x)

parseSchema ("int" :: xs)
  = case xs of
      [] => Just SInt
      _ => do x <- parseSchema xs
              Just (SInt .+. x)
                         
parseSchema ("char" :: xs)
  = case xs of
      [] => Just SChar
      _ => do x <- parseSchema xs
              Just (SChar .+. x)                           
      
parseSchema _ = Nothing


parseCommand : (schema : Schema) -> (cmd : String) -> (args : String) -> Maybe (Command schema)
parseCommand schema "schema" str = do x <- parseSchema (words str)
                                      Just (SetSchema x)

parseCommand schema "add" str  = do x <- parseBySchema schema str 
                                    Just (Add x)
                                   
parseCommand schema "get" val  = case all isDigit (unpack val) of
                                   False => Just GetAll
                                   True => Just (Get (cast val))
                                   
parseCommand schema "quit" "" = Just Quit
parseCommand _      _      _  = Nothing


parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = case span (/= ' ') input of
                       (cmd, args) => parseCommand schema cmd (ltrim args)


display : SchemaType schema -> String
display {schema = SString} item = show item
display {schema = SInt} item = show item
display {schema = SChar} item = show item
display {schema = (x .+. y)} (l,r) = display l ++ " , " ++ display r


getEntry : (p : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry p store = let store_items = items store in
                             do x <- integerToFin p (size store)
                                Just (display (index x (store_items)) ++ "\n", store)

setSchema : (store : DataStore) -> Schema -> Maybe DataStore
setSchema store schema = case size store of
                         Z => Just (MkData schema _ [])
                         (S k) => Nothing
                         

showAll : Vect n (SchemaType schema) -> Nat -> String
showAll [] k        = ""
showAll (x :: xs) k = let rest = showAll xs (k + 1) in
        show k ++ " : " ++ display x ++ rest 

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input = case parse (schema store) input of
                             Nothing => Just ("Invalid Command\n", store)
                             Just (SetSchema schema') =>
                               case setSchema store schema' of
                                 Nothing     => Just ("Can't update schema\n", store)
                                 Just store' => Just ("OK\n", store') 
                             Just (Add item) => 
                                Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
                             Just (Get x)    => getEntry x store 
                             Just GetAll     => Just (showAll (items store) 0, store)
                             Just Quit       => Nothing


main : IO ()
main = replWith (MkData SString _ []) "Command: " processInput

