||| Defines utilities for converting `String` to `RegExp`.
module Regex.String

import Text.Lexer
import Text.Parser

import Regex

%default total

-----------
-- Lexer --
-----------

data RegExpToken = Literal String
                 | OpenParen
                 | CloseParen
                 | OpenBracket
                 | CloseBracket

symbolL : Lexer
symbolL = non $ oneOf "()[]"

regExpTokens : TokenMap RegExpToken
regExpTokens = [
  (symbolL, Literal),
  (is '(', \_ => OpenParen),
  (is ')', \_ => CloseParen),
  (is '[', \_ => OpenBracket),
  (is ']', \_ => CloseBracket)
]

------------
-- Parser --
------------

Rule : Type -> Type
Rule = Grammar (TokenData RegExpToken) True

literalR : Rule (RegExp Char)
literalR = terminal
  "Expected literal"
  (\x => case tok x of
              Literal s => case unpack s of
                                [] => Nothing
                                (c::_) => Just $ Lit c
              _        => Nothing)

openParenR : Rule ()
openParenR = terminal
  "Expected '('"
  (\x => case tok x of
              OpenParen => Just ()
              _         => Nothing)

closeParenR : Rule ()
closeParenR = terminal
  "Expected ')'"
  (\x => case tok x of
              CloseParen => Just ()
              _          => Nothing)

parenR : Rule a -> Rule a
parenR expr = openParenR *> expr <* closeParenR

openBracketR : Rule ()
openBracketR = terminal
  "Expected '['"
  (\x => case tok x of
              OpenBracket => Just ()
              _           => Nothing)

closeBracketR : Rule ()
closeBracketR = terminal
  "Expected ']'"
  (\x => case tok x of
              CloseBracket => Just ()
              _            => Nothing)

bracketR : Rule (RegExp Char)
bracketR = do
  openBracketR
  lits <- some literalR
  closeBracketR
  pure $ foldr Disj Empty lits

partial
exprR : Rule (RegExp Char)
exprR = (parenR exprR) <|> bracketR <|> literalR

-------------
-- toRegex --
-------------

||| Converts a `String` to a `RegExp`.
export
toRegex : String -> Maybe (RegExp Char)
toRegex s = case parse exprR $ fst $ lex regExpTokens s of
                 Left _ => Nothing
                 Right (r, _) => Just r
