||| TODO docs
module RegExp.String

import Decidable.Equality
import RegExp as RE
import public RegExp.Types as RET

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
Matches : RegExp -> String -> Type
Matches r s = RET.Matches r (unpack s)

---------------
-- OPERATORS --
---------------

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

||| Builds a `RegExp` which optionally matches another `RegExp`.
export
one : RegExp -> RegExp
one r = Star r .|. Empty

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

||| Builds a `RegExp` which matches any one of the provided characters.
export
any : (Foldable a, Functor a) => (xs : a Char) -> RegExp
any = foldr (.|.) Null . map Lit

----------------
-- SHORTHANDS --
----------------

||| Matches a lowercase ASCII character.
export
lowercase : RegExp
lowercase = 'a'...'z'

||| Matches an uppercase ASCII character.
export
uppercase : RegExp
uppercase = 'A'...'Z'

||| Matches an alphabetical ASCII character.
export
alpha : RegExp
alpha = lowercase .|. uppercase

||| Matches a numeric digit ASCII character.
export
digit : RegExp
digit = '0'...'9'

||| Matches an alphanumeric ASCII character.
export
alphaNumeric : RegExp
alphaNumeric = alpha .|. digit

||| Matches an alphanumeric or underscore ASCII character.
export
word : RegExp
word = alphaNumeric .|. lit '_'

||| Matches a whitespace ASCII character.
export
whitespace : RegExp
whitespace = any [' ', '\t', '\r', '\n', '\v', '\f']

--------------
-- MATCHING --
--------------

||| Decides whether the provided string matches a regular expression.
export
matches : (r : RegExp) -> (s : String) -> Dec (Matches r s)
matches r s = RE.matches r (unpack s)

-----------
-- TESTS --
-----------

test_range_single : 'x'...'x' = Lit 'x'
test_range_single = Refl

test_to_asc : 'a'...'c' = (Disj (Lit 'a') (Disj (Lit 'b') (Lit 'c')))
test_to_asc = Refl

test_to_desc : '3'...'1' = (Disj (Lit '1') (Disj (Lit '2') (Lit '3')))
test_to_desc = Refl
