import Data.Vect

length' : List a -> Nat
length' [] = 0
length' (x :: xs) = 1 + length' xs

reverse' : List a -> List a
reverse' [] = []
reverse' (x :: xs) = reverse xs ++ [x]

map' : (a -> b) -> List a -> List b
map' f [] = []
map' f (x :: xs) = f x :: map' f xs

vmap' : (a -> b) -> Vect n a -> Vect n b
vmap' f [] = []
vmap' f (x :: xs) = f x :: vmap' f xs

createEmpties : Vect n (Vect 0 elem)
createEmpties = replicate _ []

transposeHelp : (x : Vect n elem) -> 
                (xstrans : Vect n (Vect len elem)) -> 
                Vect n (Vect (S len) elem)
transposeHelp x [] = []
transposeHelp (x :: ys) (y :: xs) = (x :: y) :: transposeHelp ys xs

transposeMat : Vect m (Vect n elem) -> Vect n (Vect m elem)
transposeMat [] = createEmpties
transposeMat (x :: xs) = let xstrans = transposeMat xs in
                             transposeHelp x xstrans
