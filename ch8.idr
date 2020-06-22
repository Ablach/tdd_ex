same_cons : {xs : List a} -> {ys : List a} ->
            xs = ys -> x :: xs = x :: ys
same_cons prf = cong prf

same_lists : {xs : List a} -> {ys : List a} ->
             x = y -> xs = ys -> x :: xs = y :: ys
same_lists Refl prf1 = cong prf1

data ThreeEq : a -> b -> c -> Type where
     Same : ThreeEq a a a

allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z) 
allSameS z z z Same = Same

data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a
%name Vect xs, ys

(++) : Vect n elem -> Vect m elem -> Vect (n + m) elem
(++) [] y = y
(++) (x :: xs) ys = x :: (xs ++ ys)

{-
myReverse : Vect n elem -> Vect n elem
myReverse [] = []
myReverse (x :: xs) = reverseProof (myReverse xs ++ [x])
   where 
    reverseProof : Vect (k + 1) elem -> Vect (S k) elem
    reverseProof {k} res = rewrite plusCommutative 1 k in res
-}

myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes Z m = sym (plusZeroRightNeutral m)
myPlusCommutes (S k) m = rewrite (myPlusCommutes k m) in (plusSuccRightSucc m k)

myReverse : Vect n elem -> Vect n elem
myReverse xs = reverse' [] xs
  where reverse' : Vect n a -> Vect m a -> Vect (n + m) a
        reverse' {n} acc [] = rewrite plusZeroRightNeutral n in acc
        reverse' {n} {m = S k} acc (x :: xs) 
          = rewrite sym (plusSuccRightSucc n k) in (reverse' (x :: acc) xs)

headUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} ->
                    (contra : (x = y) -> Void) -> ((x :: xs) = (y :: ys)) ->
                    Void
headUnequal contra Refl = contra Refl

tailUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} -> 
                    (contra : (xs = ys) -> Void) -> ((x :: xs) = (y :: ys)) ->
                    Void
tailUnequal contra Refl = contra Refl 

DecEq a => DecEq (Vect n a) where
  decEq [] [] = Yes Refl
  decEq (x :: xs) (y :: ys) = case decEq x y of
                                   (Yes Refl) =>
                                      (case decEq xs ys of
                                          (Yes Refl) => Yes Refl
                                          (No contra) => No (tailUnequal contra))
                                   (No contra) => No (headUnequal contra)


