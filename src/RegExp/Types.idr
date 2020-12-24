module RegExp.Types

import Data.List
import Decidable.Equality

||| A regular expression specification.
public export
data RegExp : (0 a : Type) -> Type where
  ||| Denotes the empty set
  Null : RegExp a
  ||| Denotes the empty string
  Empty : RegExp a
  ||| Denotes a single literal character
  Lit : a -> RegExp a
  ||| Denotes concatenation
  Cat : RegExp a -> RegExp a -> RegExp a
  ||| Denotes disjunction (OR)
  Disj : RegExp a -> RegExp a -> RegExp a
  ||| Denotes conjunction (AND)
  Conj : RegExp a -> RegExp a -> RegExp a
  ||| Denotes the Kleene star
  Star : RegExp a -> RegExp a

||| The property of a regular expression matching an input string.
public export
data Matches: RegExp a -> List a -> Type where
  ||| Rule: `[]` is in `Empty`
  InEmpty : Matches Empty []
  ||| Rule: `[x]` is in `Lit x`
  InLit : {x : a} -> Matches (Lit x) [x]
  ||| Rule: If `xs` is in regular expressions `r` and `ys` is in regular expression `s`, then
  ||| `xs ++ ys` is in `Cat r s`
  InCat : {xs : List a} ->
          {ys : List a} ->
          {zs : List a} ->
          {r : RegExp a} ->
          {s : RegExp a} ->
          (p : zs = xs ++ ys) ->
          Matches r xs ->
          Matches s ys ->
          Matches (Cat r s) zs
  ||| Rule: If `xs` is in regular expression `r`, then `xs` is in `Disj r _` (i.e. left side)
  InDisjL : {xs : List a} ->
            {r : RegExp a} ->
            {s : RegExp a} ->
            Matches r xs ->
            Matches (Disj r s) xs
  ||| Rule: If `xs` is in regular expression `s`, then `xs` is in `Disj _ s` (i.e. right side)
  InDisjR : {xs : List a} ->
            {r : RegExp a} ->
            {s: RegExp a} ->
            Matches s xs ->
            Matches (Disj r s) xs
  ||| Rule: If `xs` is in regular expressions `r` and `s`, then `xs` is in `Conj r s`
  InConj : {xs : List a} ->
           {r : RegExp a} ->
           {s : RegExp a} ->
           Matches r xs ->
           Matches s xs ->
           Matches (Conj r s) xs
  ||| Rule: For all regular expression `r`, the empty string is in `Star r`.
  InStarZ : {r: RegExp a} ->
            Matches (Star r) []
  ||| Rule: If `xs` is in regular expression `r` and `ys` is in `Star r`, then `xs ++ ys` is also
  ||| in `Star r`.
  InStarS : {xs : List a} ->
            {ys : List a} ->
            {zs : List a} ->
            {r : RegExp a} ->
            (p : zs = xs ++ ys) ->
            Matches r xs ->
            Matches (Star r) ys ->
            Matches (Star r) (xs ++ ys)

export
Uninhabited (Matches Null xs) where
  uninhabited _ impossible

export
Uninhabited (Matches Empty (x::xs)) where
  uninhabited _ impossible

export
Uninhabited (Matches (Lit x) []) where
  uninhabited _ impossible

----------------------------------------------------------------------------------------------------
-- Interface Implementations                                                                      --
----------------------------------------------------------------------------------------------------

export
DecEq a => DecEq (RegExp a) where
  decEq Null Null = Yes Refl
  decEq (Lit x) (Lit y) with (decEq x y)
    decEq (Lit x) (Lit x) | (Yes Refl)  = Yes Refl
    decEq (Lit x) (Lit y) | (No contra) = No $ \p => case p of
                                                     Refl => contra Refl
  decEq (Cat r s) (Cat t u) with (decEq r t)
    decEq (Cat r s) (Cat r u) | (Yes Refl) with (decEq s u)
      decEq (Cat r s) (Cat r s) | (Yes Refl) | (Yes Refl) = Yes Refl
      decEq (Cat r s) (Cat r u) | (Yes Refl) | (No contra) = No $ \p => case p of
                                                                             Refl => contra Refl
    decEq (Cat r s) (Cat t u) | (No contra) = No \p => case p of
                                                            Refl => contra Refl
  decEq (Disj r s) (Disj t u) with (decEq r t)
    decEq (Disj r s) (Disj r u) | (Yes Refl) with (decEq s u)
      decEq (Disj r s) (Disj r s) | (Yes Refl) | (Yes Refl)  = Yes Refl
      decEq (Disj r s) (Disj r u) | (Yes Refl) | (No contra) = No $ \p => case p of
                                                                               Refl => contra Refl
    decEq (Disj r s) (Disj t u) | (No contra) = No $ \p => case p of
                                                                Refl => contra Refl
  decEq (Conj r s) (Conj t u) with (decEq r t)
    decEq (Conj r s) (Conj r u) | (Yes Refl) with (decEq s u)
      decEq (Conj r s) (Conj r s) | (Yes Refl) | (Yes Refl)  = Yes Refl
      decEq (Conj r s) (Conj r u) | (Yes Refl) | (No contra) = No $ \p => case p of
                                                                               Refl => contra Refl
    decEq (Conj r s) (Conj t u) | (No contra) = No $ \p => case p of
                                                                Refl => contra Refl
  decEq (Star r) (Star s) with (decEq r s)
    decEq (Star r) (Star r) | (Yes Refl) = Yes Refl
    decEq (Star r) (Star s) | (No contra) = No $ \p => case p of
                                                            Refl => contra Refl
  -- This is plain old structural equality, so I figure it's better to use a `believe_me` catch-all
  -- than to write out a million trivial `No` cases.
  decEq _ _ = No believe_me

----------------------------------------------------------------------------------------------------
-- Proofs                                                                                         --
----------------------------------------------------------------------------------------------------

||| Proof that if the result of a concatenation is empty, then both inputs are empty
appendOutputNil : {xs : List a} ->
                  {ys : List a} ->
                  xs ++ ys = [] ->
                  (xs = [], ys = [])
appendOutputNil {xs=[]} {ys=[]}    p = (Refl, Refl)
appendOutputNil {xs=[]} {ys=y::ys} p = absurd p
appendOutputNil {xs=(x::xs)} {ys}  p = absurd p

||| Proof that if an `Empty` regular expression matches a string, then the string is empty.
export
emptyMatch_implies_emptyList : Matches Empty xs -> xs = []
emptyMatch_implies_emptyList InEmpty = Refl

||| Proof that for all `Lit x` matches, `x` is equal to the head of the string.
export
litMatches_implies_headEqual : DecEq a =>
                               {x : a} ->
                               {y : a} ->
                               {ys : List a} ->
                               Matches (Lit x) (y::ys) ->
                               x = y
litMatches_implies_headEqual {x} {y=x} {ys=[]} InLit = Refl

||| Proof that if `Lit` matches `x::xs`, then `xs = []`
export
litMatchesCons_implies_restEmpty : Matches (Lit x) (x::xs) -> xs = []
litMatchesCons_implies_restEmpty InLit = Refl

||| Proof that if the `Cat r s` matches empty, then both `r` and `s` also match empty
export
catNotEmpty : {r : RegExp a} ->
              {s : RegExp a} ->
              Matches (Cat r s) [] ->
              (Matches r [], Matches s [])
catNotEmpty (InCat p r s) with (appendOutputNil $ sym p)
  catNotEmpty (InCat p r s) | (Refl, Refl) = (r, s)

||| Proof that if `Disj r s` matches empty, then at least one of `r` and `s` matches empty
export
disjNotEmpty : {r : RegExp a} ->
               {s : RegExp a} ->
               Matches (Disj r s) [] ->
               Either (Matches r []) (Matches s [])
disjNotEmpty (InDisjL r) = Left r
disjNotEmpty (InDisjR r) = Right r

||| Proof that if the `Conj r s` matches empty, then both `r` and `s` also match empty
export
conjNotEmpty : {r : RegExp a} ->
               {s : RegExp a} ->
               Matches (Conj r s) [] ->
               (Matches r [], Matches s [])
conjNotEmpty (InConj r s) = (r, s)
