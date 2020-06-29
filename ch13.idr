import Data.Vect

data DoorState = DoorClosed | DoorOpen

data DoorCmd : Type ->
               DoorState ->
               DoorState ->
               Type where
     Open : DoorCmd () DoorClosed DoorOpen
     Close : DoorCmd () DoorOpen DoorClosed
     RingBell : DoorCmd () st st
             
namespace door
          Pure : ty -> DoorCmd ty st st
          (>>=) : DoorCmd a s1 s2 -> (a -> DoorCmd b s2 s3) ->
                  DoorCmd b s1 s3             
                       
doorProg : DoorCmd () DoorClosed DoorClosed
doorProg = do RingBell
              Open
              RingBell
              Close             

data GuessCmd : Type -> Nat -> Nat -> Type where 
     Try : Integer -> GuessCmd Ordering (S k) k

namespace guess
          Pure : ty -> GuessCmd ty st st
          (>>=) : GuessCmd a s1 s2 -> (a -> GuessCmd b s2 s3) ->
                  GuessCmd b s1 s3  

threeGuesses : GuessCmd () 3 0
threeGuesses = do Try 10
                  Try 20
                  Try 15
                  Pure ()
{-
noGuesses : GuessCmd () 0 0
noGuesses = do Try 10
               pure ()
-}

data Matter = Solid | Liquid | Gas

data MatterCmd : Type -> Matter -> Matter -> Type where
     Melt : MatterCmd () Solid Liquid
     Boil : MatterCmd () Liquid Gas
     Condense : MatterCmd () Gas Liquid
     Freeze : MatterCmd () Liquid Solid
     
namespace matter
          Pure : ty -> MatterCmd ty st st
          (>>=) : MatterCmd a s1 s2 -> (a -> MatterCmd b s2 s3) ->
                  MatterCmd b s1 s3
               
iceSteam : MatterCmd () Solid Gas 
iceSteam = do Melt
              Boil

steamIce : MatterCmd () Gas Solid                             
steamIce = do Condense
              Freeze

{-              
overMelt : MatterCmd () Solid Gas
overMelt = do Melt
              Melt
-}

data StackCmd : Type -> Nat -> Nat -> Type where
     Push : Integer -> StackCmd () height (S height)
     Pop : StackCmd Integer (S height) height
     Peek : StackCmd Integer (S height) (S height)
     
     GetStr : StackCmd String height height
     PutStr : String -> StackCmd  () height height
     
     Pure : ty -> StackCmd ty height height
     (>>=) : StackCmd a h1 h2 -> (a -> StackCmd b h2 h3) ->
             StackCmd b h1 h3

runStack : (stk : Vect in_h Integer) ->
           StackCmd ty in_h out_h ->
           IO (ty, Vect out_h Integer)
runStack stk GetStr = do x <- getLine
                         pure (x, stk)
runStack stk (PutStr x) = do putStr x
                             pure ((), stk)
runStack stk (Push x) = pure ((), x :: stk)
runStack (x :: xs) Pop = pure (x, xs)
runStack (x :: xs) Peek = pure (x, x :: xs)
runStack stk (Pure x) = pure (x, stk)
runStack stk (cmd >>= nxt) 
         = do (res, newStk) <- runStack stk cmd
              runStack newStk (nxt res)

data StackIO : Nat -> Type where
     Do : StackCmd a h1 h2 -> (a -> Inf (StackIO h2)) -> 
          StackIO h1
          
namespace StackDo
          (>>=) : StackCmd a h1 h2 -> (a -> Inf (StackIO h2)) -> 
                  StackIO h1       
          (>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel 
forever = More forever

run : Fuel -> Vect height Integer -> StackIO height -> IO ()
run Dry xs y = pure ()
run (More x) xs (Do c f) = do (res, newStk) <- runStack xs c
                              run x newStk (f res)

data StkInput = Number Integer
              | Add
              | Mul
              | Sub
              | Neg
              | Discard
              | Dup
              
strToInput : String -> Maybe StkInput
strToInput "" = Nothing
strToInput "add" = Just Add
strToInput "mul" = Just Mul
strToInput "sub" = Just Sub
strToInput "neg" = Just Neg
strToInput "discard" = Just Discard
strToInput "dup" = Just Dup
strToInput x = if all isDigit (unpack x)
                  then Just (Number (cast x))
                  else Nothing

doOp : (Integer -> Integer -> Integer) -> StackCmd () (S (S h)) (S h)  
doOp f = do n <- Pop
            m <- Pop
            Push (f m n)            
        
doNeg : StackCmd () (S h) (S h)
doNeg = do n <- Pop
           Push (0 - n)

doDiscard : StackCmd () (S h) h                      
doDiscard = do x <- Pop
               PutStr ("Discarded " ++ show x ++ "\n")
               
doDup : StackCmd () (S h) (S(S h))
doDup = do n <- Peek
           PutStr ("Pushing " ++ show n ++ "\n")
           Push n

mutual

    tryOp : ({h : _} -> StackCmd () (S(S h)) (S h)) -> StackIO height
    tryOp {height = (S(S h))} f = do f
                                     res <- Peek
                                     PutStr (show res ++ "\n")
                                     stackCalc
    tryOp f = do PutStr "Not enough items on the stack\n"
                 stackCalc
    
    tryNeg : StackIO height
    tryNeg {height = (S k)} = do doNeg
                                 res <- Peek
                                 PutStr (show res ++ "\n")
                                 stackCalc
                                 
    tryDiscard : StackIO height
    tryDiscard {height = (S k)} = do doDiscard
                                     stackCalc                                     
    tryDup : StackIO height
    tryDup {height = (S k)} = do doDup
                                 stackCalc

    stackCalc : StackIO height
    stackCalc = do PutStr ">"
                   input <- GetStr
                   case strToInput input of
                         Nothing => do PutStr "Invalid input\n"
                                       stackCalc
                         Just (Number x) => do Push x
                                               stackCalc
                         Just Add => tryOp (doOp (+))
                         Just Mul => tryOp (doOp (*))
                         Just Sub => tryOp (doOp (-))
                         Just Neg => tryNeg
                         Just Discard => tryDiscard
                         Just Dup => tryDup
 
main : IO ()
main = run forever [] stackCalc
