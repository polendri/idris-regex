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
  -- ||| Denotes concatenation
  -- Cat : RegExp a -> RegExp a -> RegExp a
  ||| Denotes disjunction (OR)
  Disj : RegExp a -> RegExp a -> RegExp a
  -- ||| Denotes conjunction (AND)
  -- Conj : RegExp a -> RegExp a -> RegExp a
  -- ||| Denotes the Kleene star
  -- Star : RegExp a -> RegExp a
  -- ||| Denotes the complement
  -- Comp : RegExp a -> RegExp a

||| Defines the property of a regular expression matching an input string.
public export
data InRegExp: RegExp a -> List a -> Type where
  ||| Rule: `[]` is in `Empty`
  InEmpty : InRegExp Empty []
  ||| Rule: `[x]` is in `(Lit x)`
  InLit : (x : a) -> InRegExp (Lit x) [x]
  ||| Rule: If `xs` is in regular expression `rx`, then `xs` is in `(Disj rx _)` (i.e. left side)
  InDisjL : {xs : List a} ->
            (rx : RegExp a) ->
            (ry : RegExp a) ->
            (InRegExp rx xs) ->
            InRegExp (Disj rx ry) xs
  ||| Rule: If `xs` is in regular expression `ry`, then `xs` is in `(Disj _ ry)` (i.e. right side)
  InDisjR : {ys : List a} ->
            (rx : RegExp a) ->
            (ry: RegExp a) ->
            (InRegExp ry ys) ->
            InRegExp (Disj rx ry) ys
  -- SeqSpec : {xs : List a} ->
  --           {ys : List a} ->
  --           {zs : List a} ->
  --           (rx : RegExp a) ->
  --           (ry : RegExp a) ->
  --           RegExpSpec rx xs ->
  --           RegExpSpec ry ys ->
  --           zs = xs ++ ys ->
  --           RegExpSpec (Seq rx ry) zs
  -- StarSpec0 : (r: RegExp a) ->
  --             RegExpSpec (Star r) []
  -- StarSpecS : {xs : List a} ->
  --             {ys : List a} ->
  --             {zs : List a} ->
  --             (r : RegExp a) ->
  --             RegExpSpec r xs ->
  --             RegExpSpec (Star r) ys ->
  --             (zs = xs ++ ys) ->
  --             RegExpSpec (Star r) zs
  -- EmptySpec : RegExpSpec Empty []

export
DecEq a => DecEq (RegExp a) where
  decEq Null Null = Yes Refl
  decEq Null Empty = No $ \prf => case prf of
                                       Refl impossible
  decEq Null (Lit _) = No $ \prf => case prf of
                                         Refl impossible
  decEq Null (Disj _ _) = No $ \prf => case prf of
                                            Refl impossible
  decEq Empty Null = No $ \prf => case prf of
                                       Refl impossible
  decEq Empty Empty = Yes Refl
  decEq Empty (Lit _) = No $ \prf => case prf of
                                          Refl impossible
  decEq Empty (Disj _ _) = No $ \prf => case prf of
                                             Refl impossible
  decEq (Lit _) Null = No $ \prf => case prf of
                                         Refl impossible
  decEq (Lit _) Empty = No $ \prf => case prf of
                                          Refl impossible
  decEq (Lit x) (Lit y) with (decEq x y)
    decEq (Lit x) (Lit x) | (Yes Refl)  = Yes Refl
    decEq (Lit x) (Lit y) | (No contra) = No $ \prf => case prf of
                                                       Refl => contra Refl
  decEq (Lit _) (Disj _ _) = No $ \prf => case prf of
                                               Refl impossible
  decEq (Disj _ _) Null = No $ \prf => case prf of
                                            Refl impossible
  decEq (Disj _ _) Empty = No $ \prf => case prf of
                                             Refl impossible
  decEq (Disj _ _) (Lit _) = No $ \prf => case prf of
                                               Refl impossible
  decEq (Disj r s) (Disj t u) with (decEq r t)
    decEq (Disj r s) (Disj r u) | (Yes Refl) with (decEq s u)
      decEq (Disj r s) (Disj r s) | (Yes Refl) | (Yes Refl)  = Yes Refl
      decEq (Disj r s) (Disj r u) | (Yes Refl) | (No contra) = No $ \prf => case prf of
                                                                                 Refl => contra Refl
    decEq (Disj r s) (Disj t u) | (No contra) = No $ \prf => case prf of
                                                                  Refl => contra Refl

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
litMatches_implies_headEqual {x} {y=x} {ys=[]} (InLit x) = Refl

||| Proof that `Lit` cannot match the empty string
export
litMatchesEmpty_contra : InRegExp (Lit x) [] -> Void
litMatchesEmpty_contra _ impossible

||| Proof that if `Lit` matches `x::xs`, then `xs = []`
export
litMatchesCons_implies_restEmpty : InRegExp (Lit x) (x::xs) -> xs = []
litMatchesCons_implies_restEmpty (InLit x) = Refl

||| Proof that if both `Disj` inputs cannot match empty, then the `Disj` cannot match empty
export
disjWithNonEmptyInputsIsEmpty_contra : (rx : RegExp a) ->
                                       (ry : RegExp a) ->
                                       (contraX : InRegExp rx [] -> Void) ->
                                       (contraY : InRegExp ry [] -> Void) ->
                                       InRegExp (Disj rx ry) [] ->
                                       Void
disjWithNonEmptyInputsIsEmpty_contra rx ry contraX contraY (InDisjL rx ry rz) = contraX rz
disjWithNonEmptyInputsIsEmpty_contra rx ry contraX contraY (InDisjR rx ry rz) = contraY rz

||| TODO docs
export
disjMatches_implies_oneSideMatches : {xs : List a} ->
                                     (r : RegExp a) ->
                                     (s : RegExp a) ->
                                     InRegExp (Disj r s) xs ->
                                     Either (InRegExp r xs) (InRegExp s xs)
disjMatches_implies_oneSideMatches r s (InDisjL r s p) = Left p
disjMatches_implies_oneSideMatches r s (InDisjR r s p) = Right p
