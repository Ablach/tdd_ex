import System
import Data.Primitives.Views

VendState : Type
VendState = (Nat, Nat)

data Input = COIN 
           | VEND 
           | CHANGE 
           | REFILL Nat

strToInput : String -> Maybe Input
strToInput "insert" = Just COIN
strToInput "vend" = Just VEND
strToInput "change" = Just CHANGE
strToInput x = if all isDigit (unpack x)
                  then Just (REFILL (cast x))
                  else Nothing

data CoinResult = Success | Fail

data MachineCmd : (ty : Type) -> VendState -> (ty -> VendState) -> Type where
     InsertCoin : MachineCmd CoinResult (pounds, chocs)
                             (\res => (case res of
                                            Success => ((S pounds), chocs)
                                            Fail => (pounds, chocs)))
     Vend       : MachineCmd () (S pounds, S chocs) (const (S pounds, chocs))
     GetCoins   : MachineCmd () (pounds, chocs)     (const (Z, chocs))

     Display : String -> MachineCmd () state (const state)
     Refill : (bars : Nat) -> MachineCmd () (Z, chocs) (const (Z, bars + chocs))

     GetInput : MachineCmd (Maybe Input) state (const state) 

     Pure : ty -> MachineCmd ty state(const state)
     (>>=) : MachineCmd a state1 state2 -> ((res : a) -> MachineCmd b (state2 res) state3) ->
             MachineCmd b state1 state3

data MachineIO : VendState -> Type where
     Do : MachineCmd a state1 state2 ->
          ((res: a) -> Inf (MachineIO (state2 res))) -> MachineIO state1

getCoinResult : Integer -> CoinResult
getCoinResult x with (divides x 10)
  getCoinResult ((10 * div) + rem) | (DivBy prf) = if rem == 0 
                                                      then Fail 
                                                      else Success

runMachine : MachineCmd ty inState outState_fn -> IO ty
runMachine InsertCoin = do putStrLn "Coin inserted"
                           n <- time
                           pure (getCoinResult n)
runMachine Vend = do putStrLn "Please take your chocolate"
                     pure ()
runMachine {inState = (pounds, _)} GetCoins 
           = do putStrLn (show pounds ++ " coins returned")
                pure ()
runMachine (Display x) = do putStrLn x
                            pure ()
runMachine (Refill bars) 
           = do putStrLn ("Chocolate remaining: " ++ show bars)
                pure ()
runMachine  {inState = (pounds, chocs)} GetInput 
            = do putStrLn ("Coins: " ++ show pounds ++ "; " ++
                           "Stock: " ++ show chocs)
                 putStr "> "
                 x <- getLine
                 pure (strToInput x)
runMachine (Pure x) = pure x
runMachine (cmd >>= prog) = do x <- runMachine cmd
                               runMachine (prog x)

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

run : Fuel -> MachineIO state -> IO ()
run (More fuel) (Do c f) 
     = do res <- runMachine c
          run fuel (f res)
run Dry p = pure ()


namespace MachineDo
  (>>=) : MachineCmd a state1 state2 ->
          ((res : a) -> Inf (MachineIO (state2 res))) -> MachineIO state1
  (>>=) = Do

mutual
  vend : MachineIO (pounds, chocs)
  vend {pounds = S p} {chocs = S c} = do Vend
                                         Display "Enjoy!"
                                         machineLoop
  vend {pounds = Z} = do Display "Insert a coin"
                         machineLoop
  vend {chocs = Z} = do Display "Out of stock"
                        machineLoop

  refill : (num : Nat) -> MachineIO (pounds, chocs)
  refill {pounds = Z} num = do Refill num
                               machineLoop
  refill _ = do Display "Can't refill: Coins in machine"
                machineLoop

  machineLoop : MachineIO (pounds, chocs)
  machineLoop =
       do Just x <- GetInput | Nothing => do Display "Invalid input"
                                             machineLoop
          case x of
              COIN => do res <- InsertCoin
                         case res of
                              Success => machineLoop
                              Fail => machineLoop
              VEND => vend
              CHANGE => do GetCoins
                           Display "Change returned"
                           machineLoop
              REFILL num => refill num

main : IO ()
main = run forever (machineLoop {pounds = 0} {chocs = 1})
