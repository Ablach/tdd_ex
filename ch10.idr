import Data.List.Views as L
import Data.Vect
import Data.Vect.Views as V
import Data.Nat.Views as N

data TakeN : List a -> Type where
  Fewer : TakeN xs
  Exact : (n_xs : List a) -> TakeN (n_xs ++ rest)

total
takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN _ [] = Fewer
takeN Z xs = Exact []
takeN (S k) (x :: xs) = case takeN k xs of
                             Fewer => Fewer
                             (Exact n_xs) => Exact (x :: n_xs)

groupByN : (n : Nat) -> (xs : List a) -> List (List a)
groupByN n xs with (takeN n xs)
  groupByN n xs | Fewer = [xs]
  groupByN n (n_xs ++ rest) | (Exact n_xs) = n_xs :: groupByN n rest

halves : List a -> (List a, List a)
halves xs with (takeN (size xs `div` 2) xs)
  halves xs | Fewer = ([], xs)
  halves (n_xs ++ rest) | (Exact n_xs) = (n_xs, rest)

equalSuffix : Eq a => List a -> List a -> List a
equalSuffix xs ys with (L.snocList xs)
  equalSuffix [] ys | Empty = []
  equalSuffix (zs ++ [x]) ys | (Snoc rec) with (snocList ys)
    equalSuffix (zs ++ [x]) [] | (Snoc rec) | Empty = []
    equalSuffix (zs ++ [x]) (xs ++ [y]) | (Snoc rec) | (Snoc z)
     = case x == y of
            False => []
            True => (equalSuffix zs zs) ++ [x]

mergeSort : Ord a => Vect n a -> Vect n a
mergeSort xs with (V.splitRec xs)
  mergeSort [] | SplitRecNil = []
  mergeSort [x] | SplitRecOne = [x]
  mergeSort (ys ++ zs) | (SplitRecPair lrec rrec)
             = merge (mergeSort ys | lrec) (mergeSort zs | rrec)


toBinary : Nat -> String
toBinary k with (N.halfRec k)
  toBinary Z | HalfRecZ = ""
  toBinary (n + n) | (HalfRecEven rec) =  (toBinary n | rec) ++ "0"
  toBinary (S (n + n)) | (HalfRecOdd rec) = (toBinary n | rec) ++ "1"

palindrome : Eq a => List a -> Bool
palindrome xs with (L.vList xs)
  palindrome [] | VNil = True
  palindrome [x] | VOne = True
  palindrome (x :: (ys ++ [y])) | (VCons rec) = case x == y of
                                                     False => False
                                                     True => palindrome ys | rec


