module Lesson13.Door1

%default total

data Door = Open | Closed

openDoor : Door -> Door
openDoor _ = Open

closeDoor : Door -> Door
closeDoor _ = Closed

ringBell : Door -> Door
ringBell x = x

openDoor'' : Door -> Door
openDoor'' x = x

openDoor' : Door -> Maybe Door
openDoor' Open = Nothing
openDoor' Closed = Just Open

closeDoor' : Door -> Maybe Door
closeDoor' Open = Just Closed
closeDoor' Closed = Nothing

ringBell' : Door -> Maybe Door
ringBell' Open = Nothing
ringBell' Closed = Just Closed

test' : Door
test' = case ringBell' Open of
            Nothing => ?test'no_way
            (Just x) => x
