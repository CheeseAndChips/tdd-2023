module Lesson13.Door2

%default total

data DoorCmd : Type -> Type where
    Open : DoorCmd ()
    Close : DoorCmd ()
    Ring : DoorCmd ()
    (>>=) : DoorCmd a -> (a -> DoorCmd b) -> DoorCmd b
    (>>) : DoorCmd a -> DoorCmd b -> DoorCmd b

testProg : DoorCmd ()
testProg = do Ring
              Open
              Close

testProg' : DoorCmd ()
testProg' = do Open
               Open
               Close
