module Lesson13.Door3

%default total

data DoorState = DoorOpen | DoorClosed

data DoorCmd : Type -> (pre : DoorState) -> (post : DoorState) -> Type where
    Open : DoorCmd () DoorClosed DoorOpen
    Close : DoorCmd () DoorOpen DoorClosed
    Ring : DoorCmd () DoorClosed DoorClosed
    (>>=) : DoorCmd a s1 s2 -> (a -> DoorCmd b s2 s3) -> DoorCmd b s1 s3
    (>>) : DoorCmd a s1 s2 -> DoorCmd b s2 s3 -> DoorCmd b s1 s3

testProg : DoorCmd () DoorClosed DoorClosed
testProg = do Ring
              Open
              Close

failing
    testProg' : DoorCmd () DoorClosed DoorClosed
    testProg' = do  Open
                    Ring
                    Close
