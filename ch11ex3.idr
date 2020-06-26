import System
import Data.Primitives.Views

%default total

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in 
                           (seed' `shiftR` 2) :: randoms seed'

arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms seed)
  where
    bound : Int -> Int
    bound x with (divides x 12)
      bound ((12 * div) + rem) | (DivBy prf) = abs rem + 1

data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String
  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b
  Fread : String ->  Command (Either FileError String)
  Fwrite : String -> String -> Command (Either FileError ()) 
  Exit : Command ()

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace CommandDo
	(>>=) : Command a -> (a -> Command b) -> Command b
	(>>=) = Bind

namespace ConsoleDo
	(>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
	(>>=) = Do


runCommand : Command a -> IO a
runCommand (Exit) = exit 1
runCommand (Pure x) = pure x
runCommand (Fread file) = readFile file
runCommand (Fwrite file st) = writeFile file st
runCommand (Bind c f) = do res <- runCommand c
                           runCommand (f res)
runCommand (PutStr x) = putStr x
runCommand GetLine = getLine

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

run : Fuel -> ConsoleIO a -> IO (Maybe a)
run _ (Quit y) = do pure (Just y)
run Dry _      = pure Nothing
run (More x) (Do c f) = do res <- runCommand c
                           run x (f res)

mutual
  correct : Stream Int -> (score : Nat) -> (count : Nat) -> ConsoleIO Nat
  correct n score count = do PutStr "Correct!\n"
                             quiz n (score + 1) (count + 1)

  wrong : Stream Int -> Int -> (score : Nat) -> (count : Nat) -> ConsoleIO Nat
  wrong n ans score count = do PutStr ("Wrong, the answer is " ++ show ans ++ "\n")
                               quiz n score (count + 1)
  
  quiz : Stream Int -> (score : Nat) -> (count : Nat) -> ConsoleIO Nat
  quiz (n1 :: n2 :: ns) score count
       = do PutStr ("Score so far: " ++ show score ++ " of " ++ show count ++ "\n")
            PutStr (show n1 ++ " * " ++ show n2 ++ "?")
            ans <- GetLine
            if toLower ans == "quit" then Quit score else
              if (cast ans == n1 * n2)
                then correct ns score count
                else wrong ns (n1 * n2) score count

parseCommand' : List String -> Maybe (Command ())
parseCommand' ("cat" :: file :: _) 
  = Just (do Right conts <- Fread file
               | Left err => PutStr (show err)
             PutStr conts)
parseCommand' ("copy" :: src :: dest :: _) 
  = Just (do Right conts <- Fread src
               | Left err => PutStr (show err)
             success <- Fwrite dest conts
               | Left err => PutStr (show err)
             PutStr "file written")
parseCommand' ("quit" :: _) = Just Exit
parseCommand' _ = Nothing

parseCommand : String -> Maybe (Command ())
parseCommand st = parseCommand' (words st)
 

shell : ConsoleIO ()
shell = do PutStr ("$>")
           c <- GetLine
           case parseCommand c of
                Nothing => shell
                (Just cmd) => do cmd
                                 shell

partial
main : IO ()
main = do Just ok <- run forever shell
               | Nothing => putStrLn "No more fuel"
          pure ok
                                
partial
main' : IO ()
main' = do seed <- time
           Just score <- run forever (quiz (arithInputs (fromInteger seed)) 0 0)
            | Nothing => putStrLn "Ran out of fuel"
           putStrLn ("Final score: " ++ show score)
