module Main
import Data.Vect 

data DataStore : Type where
     MkData : (size : Nat) ->
              (items : Vect size String) ->
              DataStore
              
size : DataStore -> Nat             
size (MkData size' items) = size'

items : (store : DataStore) -> Vect (size store) String
items (MkData size' items') = items'

addToStore : DataStore -> String -> DataStore
addToStore (MkData size items) newItem = MkData _ (addToData items)
           where
            addToData : Vect old String -> Vect (S old) String
            addToData [] = [newItem]
            addToData (x :: xs) = x :: addToData xs

data Command = Add String
             | Search String
             | Size
             | Get Integer
             | Quit
             
parseCommand : (cmd : String) -> (args : String) -> Maybe Command
parseCommand "add"    str  = Just (Add str)
parseCommand "search" str  = Just (Search str)
parseCommand "size"   _    = Just (Size)
parseCommand "get"    val  = case all isDigit (unpack val) of
                                False => Nothing
                                True => Just (Get (cast val))
parseCommand "quit" ""     = Just Quit
parseCommand _      _      = Nothing

parse : (input : String) -> Maybe Command             
parse input = case span (/= ' ') input of
                   (cmd, args) => parseCommand cmd (ltrim args)

getEntry : (p : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry p store = let store_items = items store in
                             case integerToFin p (size store) of
                                   Nothing => Nothing
                                   (Just x) => Just (index x store_items ++ "\n", store)

searchVect : (s : String) -> (built : String)-> (store : DataStore) -> String
searchVect s built (MkData Z items)         = built
searchVect s built (MkData (S k) (x :: xs)) = case isInfixOf s x of
                                                 False => searchVect s built (MkData k xs)
                                                 True  =>
                                                    searchVect s 
                                                    (built ++ 
                                                     "ID: " ++ show k ++ "\n"
                                                     ++ x ++ "\n") 
                                                    (MkData k xs)

search : (s : String) -> (store : DataStore) -> Maybe (String, DataStore)
search s store = case searchVect s "" store of
                      "" => Just ("Substring not found", store)
                      x  => Just (x, store)

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input = case parse input of
                        Nothing => Just ("Invalid Command\n", store)
                        (Just (Add item)) => 
                              Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
                        (Just (Search str)) => search str store
                        (Just Size)         => Just (show (size store) ++ "\n", store)
                        (Just (Get x))      => getEntry x store 
                        (Just Quit)         => Nothing

main : IO ()
main = replWith (MkData _ []) "Command: " processInput
