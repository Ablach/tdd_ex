import Control.Monad.State

update : (stateType -> stateType) -> State stateType ()
update f = do state <- get
              put (f state)

increase : Nat -> State Nat ()
increase k = update (+k)

data Tree a = Empty
            | Node (Tree a) a (Tree a)

countEmpty : Tree a -> State Nat ()
countEmpty Empty = do n <- get
                      put (S n)
countEmpty (Node l x r) = do left <- countEmpty l
                             right <- countEmpty r
                             pure ()
testTree : Tree String
testTree = Node (Node (Node Empty "Jim" Empty) "Fred"
                      (Node Empty "Sheila" Empty)) "Alice"
                (Node Empty "Bob" (Node Empty "Eve" Empty))

countEmptyNode : Tree a -> State (Nat, Nat) ()
countEmptyNode Empty = do (e, n) <- get
                          put (S e, n)
countEmptyNode (Node l x r) = do (e, n) <- get
                                 put (e, S n)
                                 left <- countEmptyNode l
                                 right <- countEmptyNode r
                                 pure ()
