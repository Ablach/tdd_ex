data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double
           
           
Eq Shape where
           
  (==) (Triangle x z) (Triangle x' z') = x == x' && x == z'
  (==) (Rectangle x z) (Rectangle x' z') = x == x' && x == z'
  (==) (Circle x) (Circle x') = x == x'
  (==) _ _ = False
  (/=) x y = not (x == y)


area : Shape -> Double
area (Triangle x y) = x * y / 2
area (Rectangle x y) = x * y
area (Circle r) = pi * r * r


Ord Shape where
  compare x y = compare (area x) (area y)


testShapes : List Shape
testShapes = [Circle 3, Triangle 3 9, Rectangle 2 6, Circle 4, Rectangle 2 7]


data Expr num = Val num 
              | Add (Expr num) (Expr num)
              | Sub (Expr num) (Expr num)
              | Mul (Expr num) (Expr num)
              | Div (Expr num) (Expr num)
              | Abs (Expr num)
              

eval : (Neg num, Integral num, Abs num) => Expr num -> num
eval (Val x)   = x
eval (Add x y) = (eval x) + (eval y)
eval (Sub x y) = (eval x) - (eval y)
eval (Mul x y) = (eval x) * (eval y)
eval (Div x y) = (eval x) `div` (eval y)
eval (Abs x)   = abs (eval x)


Num ty => Num (Expr ty) where
  (+) = Add
  (*) = Mul
  fromInteger = Val . fromInteger
  

Neg ty => Neg (Expr ty) where            
  negate x = 0 - x
  (-) = Sub
  
  
Abs ty => Abs (Expr ty) where
  abs = Abs


Show ty => Show (Expr ty) where
  show (Val x)   = show x
  show (Add x y) = "(" ++ show x ++ "+" ++ show y ++ ")"
  show (Sub x y) = "(" ++ show x ++ "-" ++ show y ++ ")"
  show (Mul x y) = "(" ++ show x ++ "*" ++ show y ++ ")"
  show (Div x y) = "(" ++ show x ++ "/" ++ show y ++ ")"
  show (Abs x)   = "|" ++ show x ++ "|" 


(Integral ty, Neg ty, Abs ty, Eq ty) => Eq (Expr ty) where
  (==) x y = (eval x) == (eval y)


(Integral ty, Neg ty, Abs ty, Eq ty) => Cast (Expr ty) ty where
  cast = eval


Functor Expr where
  map func (Val x) = Val (func x)
  map func (Add x y) = Add (map func x) (map func y)
  map func (Sub x y) = Sub (map func x) (map func y)
  map func (Mul x y) = Mul (map func x) (map func y)
  map func (Div x y) = Div (map func x) (map func y)
  map func (Abs x) = Abs (map func x)


data Vect: Nat -> Type -> Type where
     Nil  : Vect Z ty
     (::) : ty -> Vect k ty -> Vect (S k) ty
     
     
Foldable (Vect n) where         
  foldr func init [] = init
  foldr func init (x :: xs) = func x (foldr func init xs)
  
  
Eq ty => Eq (Vect n ty) where          
  (==) [] [] = True
  (==) (x :: xs) (y :: ys) = x == y && xs == ys
