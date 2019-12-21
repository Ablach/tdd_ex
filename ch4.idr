import Data.Vect

data Shape = ||| A Triangle with a base and a height 
             Triangle Double Double
           | ||| A Rectangle with it's length and height
             Rectangle Double Double
           | ||| A Circle with it's radius
             Circle Double
%name Shape shape1, shape2, shape3      

area : Shape -> Double                          
area (Triangle  base   height) = 0.5 * base * height
area (Rectangle length height) = length * height
area (Circle    radius)        = pi * radius * radius

data Picture  = ||| Just a shape
                Primitive Shape
              | ||| The combination of two pictures
                Combine Picture Picture
              | ||| The picture from rotating another picture
                Rotate Double Picture
              | ||| A picture moved to a location
                Translate Double Double Picture
%name Picture pic1, pic2, pic3
                
pictureArea : Picture -> Double
pictureArea (Primitive shape1)      = area shape1
pictureArea (Combine   pic1   pic2) = pictureArea pic1 + pictureArea pic2
pictureArea (Rotate    x      pic1) = pictureArea pic1
pictureArea (Translate x   y  pic1) = pictureArea pic1

data Biggest = None | Size Double

compareBiggest : (pic1 : Biggest) -> (pic2 : Biggest) -> Biggest
compareBiggest None        pic2        = pic2
compareBiggest pic1        None        = pic1
compareBiggest s1@(Size x) s2@(Size y) = if x > y then s1 else s2

biggestTriangle : Picture -> Biggest
biggestTriangle (Primitive t@(Triangle x y)) = Size (area t)
biggestTriangle (Primitive _)                = None
biggestTriangle (Rotate    x    pic1)        = biggestTriangle pic1
biggestTriangle (Translate x y  pic1)        = biggestTriangle pic1
biggestTriangle (Combine   pic1 pic2)        = compareBiggest (biggestTriangle pic1) 
                                                              (biggestTriangle pic2)

data Tree elem = Leaf | Node (Tree elem) elem (Tree elem)
%name Tree tree1, tree2, Tree3

insert : Ord elem => elem -> Tree elem -> Tree elem
insert x Leaf                   = Node Leaf x Leaf
insert x t@(Node tree1 y tree2) = case compare x y of
                                     LT => Node (insert x tree1) y tree2
                                     EQ => t
                                     GT => Node tree1 y (insert x tree2)
data BStree : Type -> Type where
     Empty  : Ord elem => BStree elem
     Branch : Ord elem => (left : BStree elem) -> (val : elem) -> (right : BStree elem)
                      -> BStree elem
                      
binsert : Ord a => (x : a) -> (xs : BStree a) -> BStree a
binsert x Empty                     = Branch (Empty) x (Empty)
binsert x t@(Branch left val right) = case compare x val of
                                         LT => Branch (binsert x left) val right
                                         EQ => t
                                         GT => Branch left val (binsert x right)

listToTree : Ord a => List a -> BStree a
listToTree []        = Empty
listToTree (x :: xs) = binsert x (listToTree xs)

treeToList : BStree a -> List a
treeToList Empty                   = []
treeToList (Branch left val right) = (treeToList left) ++ [val] ++ treeToList right

data Iexp = IV Int
          | Add Iexp Iexp
          | Sub Iexp Iexp
          | Mul Iexp Iexp
          
eval : Iexp -> Int
eval (IV x)    = x
eval (Add x y) = (eval x) + (eval y)
eval (Sub x y) = (eval x) - (eval y)
eval (Mul x y) = (eval x) * (eval y)

maxMaybe : Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe Nothing  y        = y
maxMaybe x        Nothing  = x
maxMaybe (Just x) (Just y) = case compare x y of
                                  LT        => Just y
                                  otherwise => Just x

data Vect' : Nat -> Type -> Type where
     Nil  : Vect' Z a
     (::) : (x : a) -> (xs : Vect' k a) -> Vect' (S k) a
%name Vect' xs, ys, zs

append' : Vect' n elem -> Vect' m elem -> Vect' (n + m) elem
append' [] ys = ys
append' (x :: xs) ys = x :: append' xs ys

zip' : Vect' n a -> Vect' n b -> Vect' n (a,b)
zip' [] ys = []
zip' (x :: xs) (y :: ys) = (x,y) :: zip' xs ys 


tryIndex : Integer -> Vect n a -> Maybe a
tryIndex {n} i xs = case integerToFin i n of
                            Nothing    => Nothing
                            (Just ind) => Just (index ind xs)

data Powersource = Petrol | Pedal | Electric

data Vehicle   : Powersource -> Type where
     Bicycle   : Vehicle Pedal
     Unicycle  : Vehicle Pedal
     Car       : (fuel : Nat) -> Vehicle Petrol
     Bus       : (fuel : Nat) -> Vehicle Petrol
     Motorbike : (fuel : Nat) -> Vehicle Petrol
     
wheels : Vehicle power -> Nat
wheels Bicycle          = 2
wheels Unicycle         = 1
wheels (Car fuel)       = 4
wheels (Bus fuel)       = 4
wheels (Motorbike fuel) = 2

refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Car fuel)       = Car 100
refuel (Bus fuel)       = Bus 200
refuel (Motorbike fuel) = Motorbike 50
refuel Bicycle impossible
refuel Unicycle impossible

vectTake : (n :Nat) -> Vect (n + m) elem -> Vect n elem
vectTake Z     xs        = []
vectTake (S k) (x :: xs) = x :: vectTake k xs

sumEntries : Num a => (pos : Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries {n} pos xs ys = case integerToFin pos n of
                            Nothing => Nothing
                            (Just idx) => Just ((index idx xs) + (index idx ys))

 
