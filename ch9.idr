data LElem : a -> List a -> Type where
     Here : LElem x (x :: xs)
     There : LElem x (y :: xs)

data Last : List a -> a -> Type where
     LastOne : Last [value] value
     LastCons : (prf : Last xs value) -> Last (x :: xs) value

notInEmpty : Last [] value -> Void
notInEmpty LastOne impossible
notInEmpty (LastCons _) impossible

notInSingleton : (contra : (x = value) -> Void) -> Last [x] value -> Void
notInSingleton contra LastOne = contra Refl
notInSingleton _ (LastCons LastOne) impossible
notInSingleton _ (LastCons (LastCons _)) impossible


notInRest : (contra : Last (y :: xs) value -> Void) -> Last (x :: (y :: xs)) value -> Void
notInRest contra (LastCons prf) = contra prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)     
isLast [] value = No notInEmpty
isLast (x :: []) value = case decEq x value of
                              (Yes Refl) => Yes LastOne
                              (No contra) => No (notInSingleton contra)
isLast (x :: y :: xs) value = case isLast (y :: xs) value of
                                     (Yes prf) => Yes (LastCons prf)
                                     (No contra) => No (notInRest contra)
