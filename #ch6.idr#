import Data.Vect

Matrix : Nat -> Nat -> Type
Matrix n m = Vect n (Vect m Double)

testMatrix : Matrix 2 3
testMatrix = [[0,0,0],[0,0,0]]

data Format = Number Format
            | Dub    Format
            | Str    Format
            | Ch     Format
            | Lit    String Format
            | End
            
PrintfType : Format -> Type
PrintfType (Number   fmt) = (i : Int)    -> PrintfType fmt
PrintfType (Dub      fmt) = (d : Double) -> PrintfType fmt
PrintfType (Str      fmt) = (s : String) -> PrintfType fmt
PrintfType (Ch       fmt) = (c : Char)   -> PrintfType fmt 
PrintfType (Lit    x fmt) = PrintfType fmt
PrintfType End            = String

printfFmt : (fmt : Format) -> (acc : String) -> PrintfType fmt
printfFmt (Number fmt)     acc = \i => printfFmt fmt (acc ++ show i)
printfFmt (Dub    fmt)     acc = \d => printfFmt fmt (acc ++ show d)
printfFmt (Str    fmt)     acc = \s => printfFmt fmt (acc ++ s)
printfFmt (Ch     fmt)     acc = \c => printfFmt fmt (acc ++ show c)
printfFmt (Lit    lit fmt) acc = printfFmt fmt (acc ++ lit)
printfFmt End              acc = acc

toFormat : (xs : List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: xs) = Number  (toFormat xs)
toFormat ('%' :: 'f' :: xs) = Dub     (toFormat xs)
toFormat ('%' :: 's' :: xs) = Str     (toFormat xs)
toFormat ('%' :: 'c' :: xs) = Ch      (toFormat xs)
toFormat ('%'        :: xs) = Lit "%" (toFormat xs)
toFormat (c          :: xs) = case toFormat xs of
                                   Lit lit xs' => Lit (strCons c lit) xs'
                                   fmt         => Lit (strCons c "") fmt

printf : (fmt : String) -> PrintfType (toFormat (unpack fmt))
printf fmt = printfFmt _ ""

TupleVect : Nat -> Type -> Type
TupleVect Z elem = ()
TupleVect (S k) elem = (elem, (TupleVect k elem))

