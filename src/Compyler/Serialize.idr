module Compyler.Serialize

import Data.Vect
import Data.Vect.Elem
import Data.String
import Data.Bits
import Data.Primitives.Views

%default total

public export
getFlag : Char -> Bits8
getFlag c = (cast c) .|. 0x80

public export
interface PySerializable a where
  serializeWithoutFlag : a -> List Bits8
  serializeWithFlag : a -> List Bits8

public export
toLittleEndian : Bits32 -> Vect 4 Bits8
toLittleEndian m = let b32 = [m .&. 0xff,
                             (shiftR m 8) .&. 0xff,
                             (shiftR m 16) .&. 0xff,
                             (shiftR m 24) .&. 0xff]
                   in map cast b32

getLenList : (len : Nat) -> List Bits8
getLenList len = let len = toLittleEndian (cast $ len)
                 in case len of
                          [x, 0, 0, 0] => [x]
                          xs           => toList xs

public export
PySerializable Bits32 where
  serializeWithoutFlag x = toList (toLittleEndian x)
  serializeWithFlag x = getFlag 'i' :: serializeWithoutFlag x

public export
PySerializable (List Bits8) where
  serializeWithoutFlag x = toList (toLittleEndian (cast $ length x)) ++ x
  serializeWithFlag x = getFlag 's' :: serializeWithoutFlag x

public export
PySerializable (Vect _ Bits8) where
  serializeWithoutFlag x = serializeWithoutFlag $ toList x
  serializeWithFlag x = serializeWithFlag $ toList x

convertStrToBytes : AsList str -> List Bits8
convertStrToBytes [] = []
convertStrToBytes (c :: x) = (cast c) :: convertStrToBytes x

public export
PySerializable String where
  serializeWithoutFlag x = getLenList (length x) ++ (convertStrToBytes $ asList x)
  serializeWithFlag x = (getFlag (if length x < 256 then 'Z' else 'a')) :: serializeWithoutFlag x

public export
PySerializable (Vect _ Bits32) where
  serializeWithoutFlag x = let len = toLittleEndian (cast $ length x)
                               len_buffer = case len of
                                                [x, 0, 0, 0] => [x]
                                                xs =>           toList xs
                           in len_buffer ++ (intercalate [] (toList $ map serializeWithFlag x))
  serializeWithFlag x = (getFlag (if length x < 256 then ')' else '(')) :: serializeWithoutFlag x

public export
PySerializable (Vect _ String) where
  serializeWithoutFlag x = let len = toLittleEndian (cast $ length x)
                               len_buffer = case len of
                                                [x, 0, 0, 0] => [x]
                                                xs =>           toList xs
                           in len_buffer ++ (intercalate [] (toList $ map serializeWithFlag x))
  serializeWithFlag x = (getFlag (if length x < 256 then ')' else '(')) :: serializeWithoutFlag x
