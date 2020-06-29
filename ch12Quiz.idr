import Data.Primitives.Views
import System
import Data.String

record Score where
  constructor MkScore
  correct : Nat
  attempted : Nat

record GameState where
  constructor MkGameState
  score : Score
  difficulty : Int
  
Show GameState where
  show st = show (correct (score st)) ++ "/" ++
            show (attempted (score st)) ++ "\n" ++
            "Difficulty: " ++ show (difficulty st)

initState : GameState
initState = MkGameState (MkScore 0 0) 12

setDifficulty : Int -> GameState -> GameState
setDifficulty newDiff = record {difficulty = newDiff}

addWrong : GameState -> GameState
addWrong = record { score->attempted $= (+1) }

addCorrect : GameState -> GameState
addCorrect = record { score->attempted $= (+1), 
                      score->correct $= (+1) }

data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String

  GetRandom : Command Int
  GetGameState : Command GameState
  PutGameState : GameState -> Command ()
      
  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b

mutual
  Functor Command where
    map func x = pure func <*> x

  Applicative Command where
    pure = Pure
    (<*>) f x = do f' <- f
                   x' <- x
                   pure (f' x')
    
  Monad Command where
    (>>=) x f = Bind x f
  
data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace CommandDo
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind

namespace ConsoleDo
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

forever : Fuel
forever = More forever

runCommand : Stream Int -> GameState -> Command a ->
             IO (a, Stream Int, GameState)
runCommand rs st (PutStr x) = do putStr x
                                 pure ((), rs, st)
runCommand rs st GetLine = do str <- getLine
                              pure (str, rs, st)
runCommand (r :: rs) st GetRandom 
  = pure (getRandom r (difficulty st), rs, st)
  where
    getRandom : Int -> Int -> Int
    getRandom val max with (divides val max)
      getRandom val 0 | DivByZero = 1
      getRandom ((max * div) + rem) max | (DivBy prf) = abs rem + 1  
      
runCommand rs st GetGameState = pure (st, rs, st)
runCommand rs st (PutGameState newSt) = pure ((), rs, newSt)
runCommand rs st (Pure x) = pure (x, rs, st)
runCommand rs st (Bind c f) = do (res, newRs, newSt) <- runCommand rs st c
                                 runCommand newRs newSt (f res)

                           
run : Fuel -> Stream Int -> GameState -> ConsoleIO a -> 
      IO (Maybe a, Stream Int, GameState)
run fuel rs st (Quit x) = pure (Just x, rs, st)
run fuel rs st (Do c f) 
  = do (res, newRs, newSt) <- runCommand rs st c
       run fuel newRs newSt (f res)
run Dry rs st p = pure (Nothing, rs, st)       

randoms : Int -> Stream Int 
randoms seed = let seed' = 1664525 * seed + 1013904223 in
                (seed' `shiftR` 2) :: randoms seed'

data Input = Answer Int | QuitCmd

readInput : (prompt : String) -> Command Input
readInput prompt = do PutStr prompt
                      answer <- GetLine
                      if toLower answer == "quit"
                        then Pure QuitCmd
                        else Pure (Answer (cast answer))

updateGameState : (GameState -> GameState) -> Command ()
updateGameState f = do gs <- GetGameState
                       PutGameState (f gs)
                        

mutual
  correct : ConsoleIO GameState
  correct = do PutStr "Correct!\n"
               updateGameState addCorrect
               quiz
               
  wrong : Int -> ConsoleIO GameState
  wrong ans = do PutStr ("Wrong! The correct answer is " ++ show ans ++ "\n")
                 st <- GetGameState
                 PutGameState (addWrong st)
                 quiz
  
  quiz : ConsoleIO GameState
  quiz = do n1 <- GetRandom
            n2 <- GetRandom
            st <- GetGameState
            PutStr (show st ++ "\n")
            input <- readInput (show n1 ++ " * " ++ show n2 ++ "? ")
            (case input of
                  (Answer x) => if x == n1 * n2 
                                   then correct
                                   else wrong (n1 * n2)
                  QuitCmd => Quit st)

partial 
main : IO ()
main = do seed <- time
          (Just score, _, state) <-
            run forever (randoms (fromInteger seed)) initState quiz
              | _ => putStrLn "Ran out of fuel"
          putStrLn ("Final score: " ++ show state)
          

