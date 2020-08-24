||| Defines verified regular expressions.
|||
||| Based on https://www.ccs.neu.edu/home/turon/re-deriv.pdf
module Regex

import Decidable.Equality

import Regex.Equivalences
import public Regex.Types

%default total

infix 4 ~=

||| A regular expression is _nullable_ if the language it defines contains the empty string.
|||
||| This returns `Empty` if the input is nullable, and `Null` otherwise (formulating it this way
||| is helpful for use in `derive`)
nullable : RegExp a -> RegExp a
nullable r = if nullable' r then Empty else Null where
  nullable' : RegExp a -> Bool
  nullable' Null         = False
  nullable' Empty        = True
  nullable' (Lit _)      = False
  nullable' (Cat r s) = (nullable' r) && (nullable' s)
  nullable' (Disj r s) = (nullable' r) || (nullable' s)
  nullable' (Conj r s) = (nullable' r) && (nullable' s)
  nullable' (Star r) = True

||| Computes the derivative of a regular expression `r` with respect to a symbol `x`.
derive : (DecEq a) => (r : RegExp a) -> (x : a) -> RegExp a
derive Null _ = Null
derive Empty _ = Null
derive (Lit y) x with (decEq y x)
  derive (Lit x) x | (Yes Refl) = Empty
  derive (Lit y) x | (No _)     = Null
derive (Cat rx ry) x = normDisj (Cat (derive rx x) ry) (Cat (nullable rx) (derive ry x))
derive (Disj rx ry) x = normDisj (derive rx x) (derive ry x)
derive (Conj rx ry) x = Conj (derive rx x) (derive ry x)
derive (Star r) x = Cat (derive r x) (Star r)

||| Given a regular expression `r` and a string `xs`, determines whether `r` _matches_ `[]` (i.e.
||| whether empty is in the language of `r`).
matchEmpty : (r : RegExp a) -> Dec (InRegExp r [])
matchEmpty Null = No nullMatchesAny_contra
matchEmpty Empty = Yes InEmpty
matchEmpty (Lit x) = No $ litMatchesEmpty_contra
matchEmpty (Cat r s) = ?matchEmpty_cat_hole1
matchEmpty (Disj r s) = case (matchEmpty r, matchEmpty s) of
                             (Yes prf, _)             => Yes $ InDisjL prf
                             (_, Yes prf)             => Yes $ InDisjR prf
                             (No contraX, No contraY) => No  $ disjWithNonEmptyInputsIsEmpty_contra r s contraX contraY
matchEmpty (Conj r s) = case (matchEmpty r, matchEmpty s) of
                             (Yes pr, Yes ps) => Yes $ InConj pr ps
                             (No contra, _) => No $ ?matchEmpty_conj_hole1
                             (_, No contra) => No $ ?matchEmpty_conj_hole2
matchEmpty (Star r) = ?matchEmpty_star_hole1

||| Proof that the derivation-based match algorithm is sound: if the derivative of `r` w.r.t. `x`
||| matches `xs`, then `r` matches `(x::xs)`.
derive_isSound : DecEq a =>
                 {r : RegExp a} ->
                 {x : a} ->
                 {xs : List a} ->
                 InRegExp (derive r x) xs ->
                 InRegExp r (x::xs)
derive_isSound {r=Null}        _ impossible
derive_isSound {r=Empty}       _ impossible
derive_isSound {r=(Lit y)} {x} p with (decEq y x)
  derive_isSound {r=(Lit x)} {x} p | (Yes Refl) = rewrite emptyMatch_implies_emptyList p in InLit
  derive_isSound {r=(Lit y)} {x} p | (No _)     = absurd $ nullMatchesAny_contra p
derive_isSound {r=(Cat r s)} p = ?derive_isSound_cat_hole1
derive_isSound {r=(Disj r s)}  p with (normDisj_isSound p)
  derive_isSound {r=(Disj r s)} p | (InDisjL pr) = InDisjL $ derive_isSound pr
  derive_isSound {r=(Disj r s)} p | (InDisjR ps) = InDisjR $ derive_isSound ps
derive_isSound {r=(Conj r s)} p = ?derive_isSound_conj_hole1
derive_isSound {r=(Star r)} p = ?derive_isSound_star_hole1

||| Proof that the derivation-based match algorithm is complete: if `r` matches `x::xs`, then a
||| derivative of `r` w.r.t. `x` can be found to construct a proof.
derive_isComplete : DecEq a =>
                    {r : RegExp a} ->
                    {x : a} ->
                    {xs : List a} ->
                    InRegExp r (x::xs) ->
                    InRegExp (derive r x) xs
derive_isComplete {r=Null}       p               = absurd $ nullMatchesAny_contra p
derive_isComplete {r=Empty}      p               = absurd $ emptyMatchesNonEmpty_contra p
derive_isComplete {r=(Lit y)}    p with (decEq y x)
  derive_isComplete {r=(Lit x)} p | (Yes Refl)  = rewrite litMatchesCons_implies_restEmpty p in InEmpty
  derive_isComplete {r=(Lit y)} p | (No contra) = absurd $ contra $ litMatches_implies_headEqual p
derive_isComplete {r=(Cat r s)} p = ?derive_isComplete_cat_hole1
derive_isComplete {r=(Disj r s)} (InDisjL p) =
  normDisj_isComplete $ InDisjL $ derive_isComplete p
derive_isComplete {r=(Disj r s)} (InDisjR p) =
  normDisj_isComplete $ InDisjR $ derive_isComplete p
derive_isComplete {r=(Conj r s)} p = ?derive_isComplete_conj_hole1
derive_isComplete {r=(Star r)} p = ?derive_isComplete_star_hole1

||| Given a regular expression `r` and a string `xs`, determines whether `r` _matches_ `u` (i.e.
||| whether `xs` is in the language of `r`).
export
(~=) : DecEq a => (r : RegExp a) -> (xs : List a) -> Dec (InRegExp r xs)
(~=) r [] = matchEmpty r
(~=) r (x::xs) =
  case (derive r x) ~= xs of
    Yes prf => Yes $ derive_isSound prf
    No contra => No $ contra . derive_isComplete
