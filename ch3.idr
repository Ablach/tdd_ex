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

transposeMat : Vect m (Vect n elem) -> Vect n (Vect m elem)
transposeMat [] = createEmpties
transposeMat (x :: xs) = ?transposeMat_rhs_2
