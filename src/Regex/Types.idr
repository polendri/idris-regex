module Regex.Types

import Decidable.Equality

%default total

||| A regular expression specification.
public export
data RegExp : (a : Type) -> Type where
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

||| Defines the property of a regular expression matching an input string.
public export
data InRegExp: RegExp a -> List a -> Type where
  ||| Rule: `[]` is in `Empty`
  InEmpty : InRegExp Empty []
  ||| Rule: `[x]` is in `Lit x`
  InLit : {x : a} -> InRegExp (Lit x) [x]
  ||| Rule: If `xs` is in regular expressions `r` and `ys` is in regular expression `s`, then
  ||| `xs ++ ys` is in `Cat r s`
  InCat : {xs : List a} ->
          {ys : List a} ->
          {zs : List a} ->
          {r : RegExp a} ->
          {s : RegExp a} ->
          (p : zs = xs ++ ys) ->
          InRegExp r xs ->
          InRegExp s ys ->
          InRegExp (Cat r s) zs
  ||| Rule: If `xs` is in regular expression `r`, then `xs` is in `Disj r _` (i.e. left side)
  InDisjL : {xs : List a} ->
            {r : RegExp a} ->
            {s : RegExp a} ->
            InRegExp r xs ->
            InRegExp (Disj r s) xs
  ||| Rule: If `xs` is in regular expression `s`, then `xs` is in `Disj _ s` (i.e. right side)
  InDisjR : {xs : List a} ->
            {r : RegExp a} ->
            {s: RegExp a} ->
            InRegExp s xs ->
            InRegExp (Disj r s) xs
  ||| Rule: If `xs` is in regular expressions `r` and `s`, then `xs` is in `Conj r s`
  InConj : {xs : List a} ->
           {r : RegExp a} ->
           {s : RegExp a} ->
           InRegExp r xs ->
           InRegExp s xs ->
           InRegExp (Conj r s) xs
  ||| Rule: For all regular expression `r`, the empty string is in `Star r`.
  InStarZ : {r: RegExp a} ->
            InRegExp (Star r) []
  ||| Rule: If `xs` is in regular expression `r` and `ys` is in `Star r`, then `xs ++ ys` is also
  ||| in `Star r`.
  InStarS : {xs : List a} ->
            {ys : List a} ->
            {zs : List a} ->
            {r : RegExp a} ->
            (p : zs = xs ++ ys) ->
            InRegExp r xs ->
            InRegExp (Star r) ys ->
            InRegExp (Star r) (xs ++ ys)

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

-- TODO move into generic Proofs module
export
lemma_consNotNil : {x : t} -> {xs : List t} -> (x::xs) = [] -> Void
lemma_consNotNil Refl impossible

-- TODO move into generic Proofs module
export
lemma_appendOutputNil : {xs : List a} ->
                        {ys : List a} ->
                        [] = xs ++ ys ->
                        (xs = [], ys = [])
lemma_appendOutputNil {xs=[]} {ys=[]} p = (Refl, Refl)
lemma_appendOutputNil {xs=[]} {ys=y::ys} p = absurd $ lemma_consNotNil $ sym p
lemma_appendOutputNil {xs=(x::xs)} {ys} p = absurd $ lemma_consNotNil $ sym p

||| Proof that `Null` can't match any string
export
nullMatchesAny_contra : {xs : List a} -> InRegExp Null xs -> Void
nullMatchesAny_contra _ impossible

||| Proof that if an `Empty` regular expression matches a string, then the string is empty.
export
emptyMatch_implies_emptyList : InRegExp Empty xs -> xs = []
emptyMatch_implies_emptyList InEmpty = Refl

||| Proof that `Empty` can't match a non-empty string
export
emptyMatchesNonEmpty_contra : {x : a} -> {xs : List a} -> InRegExp Empty (x::xs) -> Void
emptyMatchesNonEmpty_contra _ impossible

||| Proof that for all `Lit x` matches, `x` is equal to the head of the string.
export
litMatches_implies_headEqual : DecEq a =>
                               {x : a} ->
                               {y : a} ->
                               {ys : List a} ->
                               InRegExp (Lit x) (y::ys) ->
                               x = y
litMatches_implies_headEqual {x} {y=x} {ys=[]} InLit = Refl

||| Proof that `Lit` cannot match the empty string
export
litMatchesEmpty_contra : InRegExp (Lit x) [] -> Void
litMatchesEmpty_contra _ impossible

||| Proof that if `Lit` matches `x::xs`, then `xs = []`
export
litMatchesCons_implies_restEmpty : InRegExp (Lit x) (x::xs) -> xs = []
litMatchesCons_implies_restEmpty InLit = Refl

||| Proof that if the `Cat r s` matches empty, then both `r` and `s` also match empty
export
lemma_catNotEmpty : {r : RegExp a} ->
                    {s : RegExp a} ->
                    InRegExp (Cat r s) [] ->
                   (InRegExp r [], InRegExp s [])
lemma_catNotEmpty (InCat p r s) with (lemma_appendOutputNil p)
  lemma_catNotEmpty (InCat p r s) | (Refl, Refl) = (r, s)

||| Proof that if `Disj r s` matches empty, then at least one of `r` and `s` matches empty
export
lemma_disjNotEmpty : {r : RegExp a} ->
                     {s : RegExp a} ->
                     InRegExp (Disj r s) [] ->
                     Either (InRegExp r []) (InRegExp s [])
lemma_disjNotEmpty (InDisjL r) = Left r
lemma_disjNotEmpty (InDisjR r) = Right r

||| Proof that if the `Conj r s` matches empty, then both `r` and `s` also match empty
export
lemma_conjNotEmpty : {r : RegExp a} ->
                     {s : RegExp a} ->
                     InRegExp (Conj r s) [] ->
                     (InRegExp r [], InRegExp s [])
lemma_conjNotEmpty (InConj r s) = (r, s)

||| Proof that if both `Disj` inputs cannot match empty, then the `Disj` cannot match empty
export
disjWithNonEmptyInputsIsEmpty_contra : (r : RegExp a) ->
                                       (s : RegExp a) ->
                                       (contraR : InRegExp r [] -> Void) ->
                                       (contraS : InRegExp s [] -> Void) ->
                                       InRegExp (Disj r s) [] ->
                                       Void
disjWithNonEmptyInputsIsEmpty_contra r s contraR contraS (InDisjL p) = contraR p
disjWithNonEmptyInputsIsEmpty_contra r s contraR contraS (InDisjR p) = contraS p
