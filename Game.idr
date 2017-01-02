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
      -> {x : a}
      -> P x
      -> All P xs
      -> All P (x::xs)

||| Remove all empty tiles from a row. The resulting row will have size no
||| greater than the input row, and is guaranteed to contain no empty tiles.
|||
||| sz - The size of the output row.
||| rem The number of filtered elements.
||| p - Proof that the count of removed tiles is equal to the input size minus
||| the output size.
||| r - The output row, guaranteed to contain only nonempty tiles.
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
        (sz ** (S rem) ** (rewrite plusSuccRightSucc sz rem in Refl) ** xs' ** allNonEmpty)
      Right nonEmpty => ((S sz) ** rem ** Refl ** x::xs' ** nonEmpty::allNonEmpty)

namespace Shifted
  ||| A shifted row has all its nonempty tiles in its head.
  data Shifted : Row n -> Type where
    Nil : {auto allEmpty : All EmptyTile row} -> Shifted row
    (::)
      : (t : Tile)
      -> {auto nonEmpty : NonEmptyTile t}
      -> Shifted row
      -> Shifted (t::row)

  ||| Construct a shifted row by joining a row consisting only of nonempty
  ||| tiles with a row consisting entirely of empty tiles.
  |||
  ||| This is essentially '(++)' for vectors (recall `Row n` is just
  ||| `Vect n Tile`) but preserving some properties on the vectors.
  joinIntoShifted
    : (nonEmpties : Row n ** All NonEmptyTile nonEmpties)
    -> (empties : Row m ** All EmptyTile empties)
    -> (row : Row (n + m) ** Shifted row)
  joinIntoShifted {n=Z} {m} (Nil ** Nil) (empties ** allEmpty) =
    (empties ** Nil)
  joinIntoShifted {n=S n'} ((ne::nes) ** (nep::neps)) es =
    let ih = joinIntoShifted (nes ** neps) es
    in let (row ** rowIsShifted) = ih
    in (ne::row ** ne::rowIsShifted)

  replicatedEmptyIsAllEmpty : All EmptyTile (replicate n Empty)
  replicatedEmptyIsAllEmpty {n=Z} = []
  replicatedEmptyIsAllEmpty {n=S n'} = EmptyIsEmpty :: replicatedEmptyIsAllEmpty

  ||| Shift a row. The output row is guaranteed to be shifted.
  shift : Row n -> (row : Row n ** Shifted row)
  shift r =
    let (n' ** rem ** Refl ** r' ** allNonEmpty) = filterEmpty r
    in joinIntoShifted
      (r' ** allNonEmpty)
      (replicate rem Empty ** replicatedEmptyIsAllEmpty)

namespace Merge
  ||| View of a row that's suitable for merging.
  data Merge : Row n -> Type where
    NoMergeEmpty : All EmptyTile row -> Merge row
    NoMergeSingleton : Merge [x]
    ||| Two equal elements can be merged, and then we need to merge the
    ||| subvector made by skipping two elements.
    ||| The equality of the elements is inlined by unification.
    MergeHere : NonEmptyTile x -> Merge xs -> Merge (x::x::xs)
    MergeSkip
      : NonEmptyTile x
      -> NonEmptyTile y
      -> Merge (y::xs)
      -> (x /= y)
      -> Merge (x::y::xs)


  ||| Merge a row. This finds sequential pairs of equal nonempty elements and
  ||| combines them deleting the second element, and incrementing the value
  ||| of the first element.
  merge : Shifted r -> Shifted r'

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
