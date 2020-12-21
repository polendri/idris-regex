||| TODO docs
module RegExp.String

import Decidable.Equality
import RegExp as RE
import RegExp.Types as RET

infixr 2 .|.
infixr 3 .&.
infixr 5 .+.
infixr 6 ...

-----------
-- TYPES --
-----------

||| A regular expression specification.
public export
RegExp : Type
RegExp = RET.RegExp Char

||| The property of a regular expression matching an input string.
public export
InRegExp : RegExp -> String -> Type
InRegExp r s = RET.InRegExp r (unpack s)

---------------
-- OPERATORS --
---------------

||| Decides whether the provided string matches a regular expression.
export
matches : (r : RegExp) -> (s : String) -> Dec (InRegExp r s)
matches r s = RE.matches r (unpack s)

||| Builds a `RegExp` matching a single character.
export
lit : Char -> RegExp
lit = Lit

||| Builds a `RegExp` as the concatenation of two other `RegExp`.
export
(.+.) : RegExp -> RegExp -> RegExp
(.+.) = Cat

||| Builds a `RegExp` as the disjunction of two other `RegExp`.
export
(.|.) : RegExp -> RegExp -> RegExp
(.|.) = Disj

||| Builds a `RegExp` as the conjunction of two other `RegExp`.
export
(.&.) : RegExp -> RegExp -> RegExp
(.&.) = Conj

||| Builds a `RegExp` which matches zero or more of another `RegExp`.
export
star : RegExp -> RegExp
star = Star

||| Builds a `RegExp` which matches one or more of another `RegExp`.
export
plus : RegExp -> RegExp
plus r = Cat r $ Star r

||| Builds a `RegExp` which matches a range of characters.
export
(...) : Char -> Char -> RegExp
(...) x y = let x' = min x y
                y' = max x y in
                to (ord x') ((ord y') - 1) (Lit y') where
  to : Int -> Int -> RegExp -> RegExp
  to min n r = if n < min
               then r
               else to min (n - 1) (Disj (Lit (chr n)) r)

----------------
-- SHORTHANDS --
----------------

export
lowercase : RegExp
lowercase = 'a'...'z'

export
uppercase : RegExp
uppercase = 'A'...'Z'

export
alpha : RegExp
alpha = lowercase .|. uppercase

export
number : RegExp
number = '0'...'9'

export
alphaNumeric : RegExp
alphaNumeric = alpha .|. number

-----------
-- TESTS --
-----------

test_range_single : 'x'...'x' = Lit 'x'
test_range_single = Refl

test_to_asc : 'a'...'c' = (Disj (Lit 'a') (Disj (Lit 'b') (Lit 'c')))
test_to_asc = Refl

test_to_desc : '3'...'1' = (Disj (Lit '1') (Disj (Lit '2') (Lit '3')))
test_to_desc = Refl
