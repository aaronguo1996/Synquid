data List a where
  Nil :: List a
  Cons :: x: a -> xs: List a -> List a

termination measure len :: List a -> {Int | _v >= 0} where
  Nil -> 0
  Cons x xs -> 1 + len xs 

measure elems :: List a -> Set a where
  Nil -> []
  Cons x xs -> [x] + elems xs

type Nat = {Int | _v >= 0}

data Word8
type ByteString = List Word8
type ByteStringNE = {ByteString | len _v > 0}

empty :: {ByteString | len _v == 0}
null :: b: ByteString -> {Bool | _v == (len b == 0)}
-- length :: b: ByteString -> {Nat | _v == (len b)}
cons :: a: Word8 -> b: ByteString -> {ByteString | (len _v) == 1 + (len b)}
snoc :: b: ByteString -> a: Word8 -> {ByteString | (len _v) == 1 + (len b)}
eq :: x: ByteString -> y: ByteString -> {Bool | _v == (x==y)}
singleton :: c:Word8 -> {ByteString | (len _v) == 1}
pack :: cs:List Word8 -> {ByteString | (len _v) == (len cs)}
unpack :: b:ByteString -> {List Word8 | (len _v) == (len b)}
head :: ByteStringNE -> Word8
tail :: b:ByteStringNE -> {ByteString | (len _v) == (len b) - 1}
last :: ByteStringNE -> Word8 -- predicate here?
init :: b:ByteStringNE -> {ByteString | (len _v) == (len b) - 1} -- all except the last one
append :: b1:ByteString -> b2:ByteString -> {ByteString | (len _v) == (len b1) + (len b2)}
intersperse :: Word8 -> b:ByteString -> {ByteString | len _v == if len b > 0 then (2 * len b - 1) else 0 }
-- qualifier {x==0,x!=0}
-- zero :: {Nat | _v == 0}
inc :: x: Int -> {Int | _v == x+1 }
dec :: x: Int -> {Int | _v == x-1 }
foldr :: <p :: List a -> b -> Bool> .
        f: (xs: List a -> x: a -> acc: {b | p xs _v} -> {b | p (Cons x xs) _v}) ->
        seed: {b | p Nil _v} ->
    ys: List a ->    
        {b | p ys _v}
rng :: n:Nat -> {List {Nat | _v <= n } | (len _v) == n + 1}

-- filter :: <p :: a -> Bool> . 
--   f:(x: a -> {Bool | _v == p x}) -> xs: List a -> { List a | elems _v == [x | x in elems xs && p x] }
-- filter = ??

findFromEndUntil :: f:(Word8 -> Bool) -> b:ByteString -> {Nat | _v <= len b}
findFromEndUntil = ??