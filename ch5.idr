import Data.Vect

readToBlank : IO (List String)
readToBlank = do 
                 c <- getLine
                 (case c of
                       "" => pure []
                       _  => do
                                cs <- readToBlank
                                pure (c :: cs)) 

readAndSave : IO ()
readAndSave = do 
                text <- readToBlank
                putStrLn("Enter the filename:")
                filename <- getLine
                Right () <- writeFile filename (unlines text)
                 | Left err => putStrLn (show err)
                pure () 


readVectFile : (filename : String) -> IO (n ** Vect n String)
readVectFile filename = do
                          Right file <- openFile filename Read
                           | Left err => pure (_ ** [])
                          Right content <- readVect file
                           | Left err => pure (_ ** [])
                          closeFile file
                          pure content
   where readVect : File -> IO (Either FileError (n ** Vect n String)) 
         readVect file = do 
                           eof <- fEOF file
                           if eof then pure (Right (_ ** [])) else do
                              Right e <- fGetLine file  
                               | Left err => pure (Left err)
                              Right (_ ** es) <- readVect file
                               | Left err => pure (Left err)
                              pure (Right (_ ** e :: es))  
 
 
 
 
