module Game

import Data.Vect
import Decidable.Equality

%default total

||| A square grid, represented as a vector of vectors.
Grid : Nat -> Type -> Type
Grid n t = Vect n (Vect n t)

||| Proposition that a Nat is nonzero.
data IsSucc : Nat -> Type where
  MkIsSucc : IsSucc (S n)

||| A tile in a 2048 board is either empty or holds a power of two greater than
||| zero.
data Tile : Type where
  Empty : Tile
  Value : (n : Nat) -> {auto p : IsSucc n} -> Tile

data NonEmptyTile : Tile -> Type where
  ValueNonEmpty : {auto p : IsSucc n} -> NonEmptyTile (Value {p} n)

data EmptyTile : Tile -> Type where
  EmptyIsEmpty : EmptyTile Empty

decEmpty : (t : Tile) -> Either (EmptyTile t) (NonEmptyTile t)
decEmpty Empty = Left EmptyIsEmpty
decEmpty (Value n) = Right ValueNonEmpty

isEmpty : Tile -> Bool
isEmpty Empty = True
isEmpty _ = False

isNonEmpty : Tile -> Bool
isNonEmpty (Value _) = True
isNonEmpty _ = False

data Horizontal : Type where
  Left : Horizontal
  Right : Horizontal

data Vertical : Type where
  Up : Vertical
  Down : Vertical

data Direction : Type where
  H : Horizontal -> Direction
  V : Vertical -> Direction

(/=) : a -> b -> Type
x /= y = Not (x = y)

Row : Nat -> Type
Row n = Vect n Tile

namespace All
  ||| Proposition that all elements of a vector satisfy a predicate.
  data All : (a -> Type) -> Vect n a -> Type where
    Nil : {P : a -> Type} -> All P []
    (::)
      : {a : Type}
      -> {P : a -> Type}
      -> (x : a)
      -> {auto p : P x}
      -> All P xs
      -> All P (x::xs)

||| Remove all empty tiles from a row. The resulting row will have size no
||| greater than the input row, and is guaranteed to contain to empty tiles.
filterEmpty
  : Row n
  -> (
    sz : Nat ** rem : Nat ** p : (sz + rem = n) ** r : Row sz ** All NonEmptyTile r
  )
filterEmpty Nil = (Z ** (Z ** (Refl ** (Nil ** (%runElab search)))))
filterEmpty (x::xs) with (filterEmpty xs)
  filterEmpty {n=sz + rem} (x::xs) | (sz ** (rem ** (Refl ** (xs' ** allNonEmpty))))
    = case decEmpty x of
      Left empty =>
        (sz ** (S rem ** (?a ** (xs' ** allNonEmpty))))
      Right nonEmpty =>
        (S sz ** (rem ** (Refl ** (?b ** nonEmpty::allNonEmpty))))

namespace Shifted
  ||| A shifted row has all its nonempty tiles in its head.
  data Shifted : Row n -> Type where
    Nil : {auto allEmpty : All EmptyTile row} -> Shifted row
    (::)
      : (t : Tile)
      -> {auto nonEmpty : NonEmptyTile t}
      -> Shifted row
      -> Shifted (t::row)

  -- shift : Row n -> (Row n ** Shifted)
  -- shift {n} row with (filter isNonEmpty row)
  --   | MkDPair len row' => row' ++ replicate (n - len) Empty

-- data Board : (Grid n Tile) -> Type where
--   NewBoard : (size : Nat) -> Board (replicate size (replicate size Empty))
--   Shift
--     : (dir : Direction)
--     -> (p : CanShiftGrid dir grid)
--     -> (b : Board grid)
--     -> Board ?a
