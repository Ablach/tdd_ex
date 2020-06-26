%default total

every_other : Stream a -> Stream a 
every_other (x :: x' :: xs) = x' :: every_other xs

data InfList : Type -> Type where
     (::) : (value : elem) -> Inf (InfList elem) -> InfList elem
%name InfList xs, ys, zs

countFrom : Integer -> InfList Integer      
countFrom x = x :: countFrom (x + 1)

getPrefix : Nat -> InfList a -> List a
getPrefix Z xs = []
getPrefix (S k) (x :: xs) = x :: getPrefix k xs

Functor InfList where
  map func (value :: xs) = func value :: map func xs

data Face : Type where
     Heads : Face
     Tails : Face 

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
	(seed' `shiftR` 2) :: randoms seed'

getFace : Int -> Face
getFace x with (x > 0)
  getFace x | False = Tails
  getFace x | True = Heads


coinFlips : (count : Nat) -> Stream Int -> List Face
coinFlips Z xs = []
coinFlips (S k) (value :: xs) = getFace value :: coinFlips k xs 

square_root_approx : (number : Double) -> (approx : Double) -> Stream Double
square_root_approx number approx 
                   = let babylonian = (approx + (number / approx)) / 2
                     in approx :: square_root_approx number babylonian

square_root_bound : (max : Nat) -> (number : Double) ->
                    (bound : Double) -> (approxs : Stream Double) ->
                    Double
                    
square_root_bound Z _ _ (value :: _) = value
square_root_bound (S k) number bound (value :: xs) 
                  with (abs (number * number - value) < bound)
  
  square_root_bound (S k) number bound (value :: xs) | True = value
  square_root_bound (S k) number bound (value :: xs) | False 
                    = square_root_bound k number bound xs

square_root : (number : Double) -> Double
square_root number = square_root_bound 100 number 0.00000000001
                                       (square_root_approx number number)

data InfIO : Type where
     Do : IO a
          -> (a -> Inf InfIO)
          -> InfIO

data Fuel = Dry | More (Lazy Fuel)

run : Fuel -> InfIO -> IO ()
run Dry y = putStrLn "Out of fuel."
run (More fuel) (Do c f) = do res <- c
                              run fuel (f res)
partial
forever : Fuel
forever = More forever

(>>=) : IO a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do

totalREPL : (prompt : String) -> (action : String -> String) -> InfIO
totalREPL prompt action = do putStr prompt
                             x <- getLine
                             putStrLn $ action x
                             totalREPL prompt action
