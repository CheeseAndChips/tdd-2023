module Lesson13.Door4

%default total

data DoorState = DoorOpen | DoorClosed
data DoorResult = OK | Jammed

data DoorCmd : (ty : Type) -> (pre : DoorState) -> (ty -> DoorState) -> Type where
    Open : DoorCmd DoorResult DoorClosed (\res => case res of
                                                     OK => DoorOpen
                                                     Jammed => DoorClosed)
    Close : DoorCmd () DoorOpen (const DoorClosed)
    Ring : DoorCmd () DoorClosed (const DoorClosed)
    (>>=) : DoorCmd a s1 s2f -> ((res : a) -> DoorCmd b (s2f res) s3f) -> DoorCmd b s1 s3f
    (>>) : DoorCmd a s1 (\_ => s2) -> DoorCmd b s2 s3f -> DoorCmd b s1 s3f
    Display : String -> DoorCmd () s (const s)
    Pure : DoorCmd () s (const s)
    Magic : DoorCmd () s1 (const s2)

testProg : DoorCmd () DoorClosed (const DoorClosed)
testProg = do Ring
              dr <- Open
              case dr of
                OK => Close
                Jammed => Pure

failing
    testProg' : DoorCmd () DoorClosed (const DoorClosed)
    testProg' = do  Ring
                    Open
                    Close
