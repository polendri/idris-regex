||| Defines verified regular expressions.
|||
||| Based on https://www.ccs.neu.edu/home/turon/re-deriv.pdf
module Regex

import Data.List
import Decidable.Equality

import Regex.Equivalences
import public Regex.Types

%default total

||| Given a regular expression `r` and a string `xs`, determines whether `r` _matches_ `[]` (i.e.
||| whether empty is in the language of `r`).
matchEmpty : (r : RegExp a) -> Dec (InRegExp r [])
matchEmpty Null = No absurd
matchEmpty Empty = Yes InEmpty
matchEmpty (Lit x) = No absurd
matchEmpty (Cat r s) = case (matchEmpty r, matchEmpty s) of
                            (Yes pr, Yes ps) => Yes $ InCat Refl pr ps
                            (No contra, _)   => No  $ contra . fst . catNotEmpty
                            (_, No contra)   => No  $ contra . snd . catNotEmpty
matchEmpty (Disj r s) = case (matchEmpty r, matchEmpty s) of
                             (Yes p, _)               => Yes $ InDisjL p
                             (_, Yes p)               => Yes $ InDisjR p
                             (No contraR, No contraS) => No  $ absurd . either contraR contraS . disjNotEmpty
matchEmpty (Conj r s) = case (matchEmpty r, matchEmpty s) of
                             (Yes pr, Yes ps) => Yes $ InConj pr ps
                             (No contra, _)   => No  $ contra . fst . conjNotEmpty
                             (_, No contra)   => No  $ contra . snd . conjNotEmpty
matchEmpty (Star r) = Yes InStarZ

||| Computes the derivative of a regular expression `r` with respect to a symbol `x`.
derive : (DecEq a) => (r : RegExp a) -> (x : a) -> RegExp a
derive Null _ = Null
derive Empty _ = Null
derive (Lit y) x with (decEq y x)
  derive (Lit x) x | (Yes Refl) = Empty
  derive (Lit y) x | (No _)     = Null
derive (Cat r s) x with (matchEmpty r)
  derive (Cat r s) x | (Yes _) = normDisj (normCat (derive r x) s) (derive s x)
  derive (Cat r s) x | (No _) = normCat (derive r x) s
derive (Disj r s) x = normDisj (derive r x) (derive s x)
derive (Conj r s) x = normConj (derive r x) (derive s x)
derive (Star r) x = normCat (derive r x) (Star r)

||| Proof that the derivation-based match algorithm is sound
derive_isSound : DecEq a =>
                 {r : RegExp a} ->
                 {x : a} ->
                 {xs : List a} ->
                 InRegExp (derive r x) xs ->
                 InRegExp r (x::xs)
derive_isSound {r=Null}  _ impossible
derive_isSound {r=Empty} _ impossible
derive_isSound {r=(Lit y)} {x} p with (decEq y x)
  derive_isSound {r=(Lit x)} {x} p | (Yes Refl) = rewrite emptyMatch_implies_emptyList p in InLit
  derive_isSound {r=(Lit y)} {x} p | (No _)     = absurd p
derive_isSound {r=(Cat r s)} {x} p with (matchEmpty r)
  derive_isSound {r=(Cat r s)} {x} p | (Yes pEmpty) with (normDisj_isSound p)
    derive_isSound {r=(Cat r s)} {x} p | (Yes pEmpty) | (InDisjL t) with (normCat_isSound t)
      derive_isSound {r=(Cat r s)} {x} p | (Yes pEmpty) | (InDisjL t) | (InCat pCat u v) = rewrite pCat in InCat Refl (derive_isSound u) v
    derive_isSound {r=(Cat r s)} {x} p | (Yes pEmpty) | (InDisjR t) = InCat Refl pEmpty (derive_isSound t)
  derive_isSound {r=(Cat r s)} {x} p | (No contra) with (normCat_isSound p)
    derive_isSound {r=(Cat r s)} {x} p | (No contra) | (InCat prf t u) = InCat (cong (x::) prf) (derive_isSound t) u
derive_isSound {r=(Disj r s)}  p with (normDisj_isSound p)
  derive_isSound {r=(Disj r s)} p | (InDisjL pr) = InDisjL $ derive_isSound pr
  derive_isSound {r=(Disj r s)} p | (InDisjR ps) = InDisjR $ derive_isSound ps
derive_isSound {r=(Conj r s)} p with (normConj_isSound p)
  derive_isSound {r=(Conj r s)} p | (InConj pr ps) = InConj (derive_isSound pr) (derive_isSound ps)
derive_isSound {r=(Star r)} p with (normCat_isSound {s=(Star r)} p)
  derive_isSound {r=(Star r)} p | (InCat prf pr prs) = rewrite prf in InStarS (cong (x::) prf) (derive_isSound pr) prs

mutual
  ||| Proof that the derivation-based match algorithm is complete for `Star`
  deriveStar_isComplete : DecEq a =>
                          {r: RegExp a} ->
                          {xs' : List a} ->
                          (x : a) ->
                          (xs : List a) ->
                          xs = x :: xs' ->
                          InRegExp (Star r) xs ->
                          InRegExp (normCat (derive r x) (Star r)) xs'
  deriveStar_isComplete _ [] p _ = absurd p
  deriveStar_isComplete {xs'} x _ p (InStarS {xs=[]} {ys} Refl pr ps) =
    deriveStar_isComplete x ys p ps
  deriveStar_isComplete x _ p (InStarS {xs=y::ys} pCat pr ps) =
    let (Refl, Refl) = consInjective p in
        normCat_isComplete $ InCat Refl (derive_isComplete pr) ps

  ||| Proof that the derivation-based match algorithm is complete
  derive_isComplete : DecEq a =>
                      {r : RegExp a} ->
                      {x : a} ->
                      {xs : List a} ->
                      InRegExp r (x::xs) ->
                      InRegExp (derive r x) xs
  derive_isComplete {r=Null}       p               = absurd p
  derive_isComplete {r=Empty}      p               = absurd p
  derive_isComplete {r=(Lit y)}    p with (decEq y x)
    derive_isComplete {r=(Lit x)} p | (Yes Refl)  = rewrite litMatchesCons_implies_restEmpty p in InEmpty
    derive_isComplete {r=(Lit y)} p | (No contra) = absurd $ contra $ litMatches_implies_headEqual p
  derive_isComplete {r=(Cat r s)} {x} {xs} p with (matchEmpty r)
    derive_isComplete {r=(Cat r s)} {x} {xs}         (InCat {xs=[]}    {ys=x::xs} Refl pr ps) | (Yes pEmpty) =
      normDisj_isComplete $ InDisjR $ derive_isComplete ps
    derive_isComplete {r=(Cat r s)} {x} {xs=xs++ys'} (InCat {xs=x::xs} {ys=ys'}   Refl pr ps) | (Yes pEmpty) =
      normDisj_isComplete $ InDisjL $ normCat_isComplete $ InCat Refl (derive_isComplete pr) ps
    derive_isComplete {r=(Cat r s)} {x} {xs}         (InCat {xs=[]}    {ys=x::xs} Refl pr ps) | (No contra)  =
      normCat_isComplete $ absurd $ contra pr
    derive_isComplete {r=(Cat r s)} {x} {xs=xs++ys'} (InCat {xs=x::xs} {ys=ys'}   Refl pr ps) | (No contra)  =
      normCat_isComplete $ InCat Refl (derive_isComplete pr) ps
  derive_isComplete {r=(Disj r s)} (InDisjL p) =
    normDisj_isComplete $ InDisjL $ derive_isComplete p
  derive_isComplete {r=(Disj r s)} (InDisjR p) =
    normDisj_isComplete $ InDisjR $ derive_isComplete p
  derive_isComplete {r=(Conj r s)} (InConj pr ps) =
    normConj_isComplete $ InConj (derive_isComplete pr) (derive_isComplete ps)
  derive_isComplete {r=(Star r)} {x} {xs} p = deriveStar_isComplete x (x::xs) Refl p

||| Given a regular expression `r` and a string `xs`, determines whether `r` _matches_ `u` (i.e.
||| whether `xs` is in the language of `r`).
export
matches : DecEq a => (xs : List a) -> (r : RegExp a) -> Dec (InRegExp r xs)
matches [] r = matchEmpty r
matches (x::xs) r =
  case matches xs (derive r x) of
    Yes prf => Yes $ derive_isSound prf
    No contra => No $ contra . derive_isComplete
