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
createEmpties {n = Z} = []
createEmpties {n = (S k)} = [] :: createEmpties

transposeHelp : (x : Vect n elem) -> 
                (xstrans : Vect n (Vect len elem)) -> 
                Vect n (Vect (S len) elem)
transposeHelp x [] = []
transposeHelp (x :: ys) (y :: xs) = (x :: y) :: transposeHelp ys xs

transposeMat : Vect m (Vect n elem) -> Vect n (Vect m elem)
transposeMat [] = createEmpties
transposeMat (x :: xs) = let xstrans = transposeMat xs in
                             transposeHelp x xstrans

transposeMat' : Vect m (Vect n elem) -> Vect n (Vect m elem)
transposeMat' [] = createEmpties
transposeMat' (x :: xs) = let xstrans = transposeMat' xs in
                              zipWith (::) x xstrans

addVect : Num a => (x : Vect m a) -> (y : Vect m a) -> Vect m a
addVect [] [] = []
addVect (x :: xs) (y :: ys) = (x + y) :: addVect xs ys

addMatrix : Num a => Vect n (Vect m a) -> Vect n (Vect m a) -> Vect n (Vect m a)
addMatrix [] [] = []
addMatrix (x :: xs) (y :: ys) = addVect x y :: addMatrix xs ys 

multCol : Num a => (x : Vect m a) -> (y : Vect m a) -> a
multCol [] [] = 0
multCol (x :: xs) (y :: ys) = (x * y) + multCol xs ys

multRow : Num a => (x : Vect m a) -> (y : Vect p (Vect m a)) -> Vect p a
multRow x [] = []
multRow x (y :: ys) = multCol x y :: multRow x ys 

multMatrix : Num a => Vect n (Vect m a) -> Vect m (Vect p a) -> Vect n (Vect p a)
multMatrix [] ys = []
multMatrix (x :: xs) right = multRow x (transposeMat' right) :: multMatrix xs right
