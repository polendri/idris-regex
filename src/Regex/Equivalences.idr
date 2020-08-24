||| Defines functions to use in place of `RegExp`'s data constructors, in order to create
||| regular expressions which are "normalized" to a canonical form as much as possible. This adds
||| some compile-time complexity but results in much smaller DFAs for testing language membership.
module Regex.Equivalences

import Decidable.Equality

import public Regex.Types

%default total

||| Defines a "normalized" `Disj`, which applies the following rules:
|||
|||   - ∅ + r ≈ r
|||   - ¬∅ + r ≈ ¬∅
|||   - r + r ≈ r
|||   - (r + s) + t ≈ r + (s + t)
|||
||| Note that the remaining equivalence (symmetry) is not captured:
|||
|||   - r + s ≈ s + r
export
normDisj : DecEq a => RegExp a -> RegExp a -> RegExp a
normDisj Null r = r
normDisj r Null = r
normDisj r s with (decEq r s)
  normDisj r          r | (Yes Refl) = r
  normDisj (Disj r s) t | (No _)     = Disj r (Disj s t)
  normDisj r          s | (No _)     = Disj r s

||| Proof (by exhaustion) that `normDisj` is sound.
export
normDisj_isSound : DecEq a =>
                   {xs : List a} ->
                   {r : RegExp a} ->
                   {s : RegExp a} ->
                   InRegExp (normDisj r s) xs ->
                   InRegExp (Disj r s) xs
normDisj_isSound {r=Null}       {s}            p                     = InDisjR p
normDisj_isSound {r=Empty}      {s=Null}       p                     = InDisjL p
normDisj_isSound {r=Empty}      {s=Empty}      p                     = p
normDisj_isSound {r=Empty}      {s=(Lit _)}    p                     = p
normDisj_isSound {r=Empty}      {s=(Cat _ _)}  p                     = p
normDisj_isSound {r=Empty}      {s=(Disj _ _)} p                     = p
normDisj_isSound {r=Empty}      {s=(Conj _ _)} p                     = p
normDisj_isSound {r=Empty}      {s=(Star _)}   p                     = p
normDisj_isSound {r=(Lit _)}    {s=Null}       p                     = InDisjL p
normDisj_isSound {r=(Lit _)}    {s=Empty}      p                     = p
normDisj_isSound {r=(Lit x)}    {s=(Lit y)}    p with (decEq x y)
  normDisj_isSound {r=(Lit x)}  {s=(Lit x)}    p | (Yes Refl)        = InDisjL p
  normDisj_isSound {r=(Lit x)}  {s=(Lit y)}    p | (No _)       = p
normDisj_isSound {r=(Lit _)}    {s=(Cat _ _)}  p                     = p
normDisj_isSound {r=(Lit _)}    {s=(Disj _ _)} p                     = p
normDisj_isSound {r=(Lit _)}    {s=(Conj _ _)} p                     = p
normDisj_isSound {r=(Lit _)}    {s=(Star _)}   p                     = p
normDisj_isSound {r=(Cat _ _)}  {s=Null}       p                     = InDisjL p
normDisj_isSound {r=(Cat _ _)}  {s=Empty}      p                     = p
normDisj_isSound {r=(Cat _ _)}  {s=(Lit _)}    p                     = p
normDisj_isSound {r=(Cat r s)}  {s=(Cat t u)}  p with (decEq r t)
  normDisj_isSound {r=(Cat r s)} {s=(Cat r u)} p | (Yes Refl) with (decEq s u)
    normDisj_isSound {r=(Cat r s)} {s=(Cat r s)} p | (Yes Refl) | (Yes Refl) = InDisjL p
    normDisj_isSound {r=(Cat r s)} {s=(Cat r u)} p | (Yes Refl) | (No _) = p
  normDisj_isSound {r=(Cat r s)} {s=(Cat t u)} p | (No _) = p
normDisj_isSound {r=(Cat _ _)}  {s=(Disj _ _)} p                     = p
normDisj_isSound {r=(Cat _ _)}  {s=(Conj _ _)} p                     = p
normDisj_isSound {r=(Cat _ _)}  {s=(Star _)}   p                     = p
normDisj_isSound {r=(Disj _ _)} {s=Null}       p                     = InDisjL p
normDisj_isSound {r=(Disj _ _)} {s=Empty}      (InDisjL p)           = InDisjL (InDisjL p)
normDisj_isSound {r=(Disj _ _)} {s=Empty}      (InDisjR (InDisjL p)) = InDisjL (InDisjR p)
normDisj_isSound {r=(Disj _ _)} {s=Empty}      (InDisjR (InDisjR p)) = InDisjR p
normDisj_isSound {r=(Disj _ _)} {s=(Lit _)}    (InDisjL p)           = InDisjL (InDisjL p)
normDisj_isSound {r=(Disj _ _)} {s=(Lit _)}    (InDisjR (InDisjL p)) = InDisjL (InDisjR p)
normDisj_isSound {r=(Disj _ _)} {s=(Lit _)}    (InDisjR (InDisjR p)) = InDisjR p
normDisj_isSound {r=(Disj _ _)} {s=(Cat _ _)}  (InDisjL p)           = InDisjL (InDisjL p)
normDisj_isSound {r=(Disj _ _)} {s=(Cat _ _)}  (InDisjR (InDisjL p)) = InDisjL (InDisjR p)
normDisj_isSound {r=(Disj _ _)} {s=(Cat _ _)}  (InDisjR (InDisjR p)) = InDisjR p
normDisj_isSound {r=(Disj r s)} {s=(Disj t u)} p with (decEq r t)
  normDisj_isSound {r=(Disj r s)} {s=(Disj r u)} p                     | (Yes Refl) with (decEq s u)
    normDisj_isSound {r=(Disj r s)} {s=(Disj r s)} p                     | (Yes Refl) | (Yes Refl) = InDisjL p
    normDisj_isSound {r=(Disj r s)} {s=(Disj r u)} (InDisjL p)           | (Yes Refl) | (No _)     = InDisjL (InDisjL p)
    normDisj_isSound {r=(Disj r s)} {s=(Disj r u)} (InDisjR (InDisjL p)) | (Yes Refl) | (No _)     = InDisjL (InDisjR p)
    normDisj_isSound {r=(Disj r s)} {s=(Disj r u)} (InDisjR (InDisjR p)) | (Yes Refl) | (No _)     = InDisjR p
  normDisj_isSound {r=(Disj r s)} {s=(Disj t u)} (InDisjL p)           | (No _) = InDisjL (InDisjL p)
  normDisj_isSound {r=(Disj r s)} {s=(Disj t u)} (InDisjR (InDisjL p)) | (No _) = InDisjL (InDisjR p)
  normDisj_isSound {r=(Disj r s)} {s=(Disj t u)} (InDisjR (InDisjR p)) | (No _) = InDisjR p
normDisj_isSound {r=(Disj _ _)} {s=(Conj _ _)} (InDisjL p)           = InDisjL (InDisjL p)
normDisj_isSound {r=(Disj _ _)} {s=(Conj _ _)} (InDisjR (InDisjL p)) = InDisjL (InDisjR p)
normDisj_isSound {r=(Disj _ _)} {s=(Conj _ _)} (InDisjR (InDisjR p)) = InDisjR p
normDisj_isSound {r=(Disj _ _)} {s=(Star _)}   (InDisjL p)           = InDisjL (InDisjL p)
normDisj_isSound {r=(Disj _ _)} {s=(Star _)}   (InDisjR (InDisjL p)) = InDisjL (InDisjR p)
normDisj_isSound {r=(Disj _ _)} {s=(Star _)}   (InDisjR (InDisjR p)) = InDisjR p
normDisj_isSound {r=(Conj _ _)} {s=Null}       p                     = InDisjL p
normDisj_isSound {r=(Conj _ _)} {s=Empty}      p                     = p
normDisj_isSound {r=(Conj _ _)} {s=(Lit _)}    p                     = p
normDisj_isSound {r=(Conj _ _)} {s=(Cat _ _)}  p                     = p
normDisj_isSound {r=(Conj _ _)} {s=(Disj _ _)} p                     = p
normDisj_isSound {r=(Conj r s)} {s=(Conj t u)} p with (decEq r t)
  normDisj_isSound {r=(Conj r s)} {s=(Conj r u)} p | (Yes Refl) with (decEq s u)
    normDisj_isSound {r=(Conj r s)} {s=(Conj r s)} p | (Yes Refl) | (Yes Refl) = InDisjL p
    normDisj_isSound {r=(Conj r s)} {s=(Conj r u)} p | (Yes Refl) | (No _) = p
  normDisj_isSound {r=(Conj r s)} {s=(Conj t u)} p | (No _) = p
normDisj_isSound {r=(Conj _ _)} {s=(Star _)}   p                     = p
normDisj_isSound {r=(Star _)}   {s=Null}       p                     = InDisjL p
normDisj_isSound {r=(Star _)}   {s=Empty}      p                     = p
normDisj_isSound {r=(Star _)}   {s=(Lit _)}    p                     = p
normDisj_isSound {r=(Star _)}   {s=(Cat _ _)}  p                     = p
normDisj_isSound {r=(Star _)}   {s=(Disj _ _)} p                     = p
normDisj_isSound {r=(Star _)}   {s=(Conj _ _)} p                     = p
normDisj_isSound {r=(Star r)}   {s=(Star s)}   p with (decEq r s)
  normDisj_isSound {r=(Star r)} {s=(Star r)}   p | (Yes Refl)        = InDisjL p
  normDisj_isSound {r=(Star r)} {s=(Star s)}   p | (No _)            = p

||| Proof (by exhaustion) that `normDisj` is complete.
export
normDisj_isComplete : DecEq a =>
                      {xs : List a} ->
                      {r : RegExp a} ->
                      {s : RegExp a} ->
                      InRegExp (Disj r s) xs ->
                      InRegExp (normDisj r s) xs
normDisj_isComplete {r=Null}       {s=_}          (InDisjL p)           = absurd $ nullMatchesAny_contra p
normDisj_isComplete {r=Null}       {s=_}          (InDisjR p)           = p
normDisj_isComplete {r=Empty}      {s=Null}       (InDisjL p)           = p
normDisj_isComplete {r=Empty}      {s=Null}       (InDisjR p)           = absurd $ nullMatchesAny_contra p
normDisj_isComplete {r=Empty}      {s=Empty}      (InDisjL p)           = InDisjL p
normDisj_isComplete {r=Empty}      {s=Empty}      (InDisjR p)           = InDisjR p
normDisj_isComplete {r=Empty}      {s=(Lit _)}    p                     = p
normDisj_isComplete {r=Empty}      {s=(Cat _ _)}  p                     = p
normDisj_isComplete {r=Empty}      {s=(Disj _ _)} p                     = p
normDisj_isComplete {r=Empty}      {s=(Conj _ _)} p                     = p
normDisj_isComplete {r=Empty}      {s=(Star _)}   p                     = p
normDisj_isComplete {r=(Lit _)}    {s=Null}       (InDisjL p)           = p
normDisj_isComplete {r=(Lit _)}    {s=Null}       (InDisjR p)           = absurd $ nullMatchesAny_contra p
normDisj_isComplete {r=(Lit _)}    {s=Empty}      p                     = p
normDisj_isComplete {r=(Lit x)}    {s=(Lit y)}    p with (decEq x y)
  normDisj_isComplete {r=(Lit x)}  {s=(Lit x)}    (InDisjL p) | (Yes Refl) = p
  normDisj_isComplete {r=(Lit x)}  {s=(Lit x)}    (InDisjR p) | (Yes Refl) = p
  normDisj_isComplete {r=(Lit x)}  {s=(Lit y)}    p           | (No _)     = p
normDisj_isComplete {r=(Lit _)}    {s=(Cat _ _)} p                      = p
normDisj_isComplete {r=(Lit _)}    {s=(Disj _ _)} p                     = p
normDisj_isComplete {r=(Lit _)}    {s=(Conj _ _)} p                     = p
normDisj_isComplete {r=(Lit _)}    {s=(Star _)} p                       = p
normDisj_isComplete {r=(Cat _ _)}  {s=Null} (InDisjL p)                 = p
normDisj_isComplete {r=(Cat _ _)}  {s=Null} (InDisjR p)                 = absurd $ nullMatchesAny_contra p
normDisj_isComplete {r=(Cat _ _)}  {s=Empty} p = p
normDisj_isComplete {r=(Cat _ _)}  {s=(Lit _)} p = p
normDisj_isComplete {r=(Cat r s)}  {s=(Cat t u)} p with (decEq r t)
  normDisj_isComplete {r=(Cat r s)} {s=(Cat r u)} p | (Yes Refl) with (decEq s u)
    normDisj_isComplete {r=(Cat r s)} {s=(Cat r s)} (InDisjL p) | (Yes Refl) | (Yes Refl) = p
    normDisj_isComplete {r=(Cat r s)} {s=(Cat r s)} (InDisjR p) | (Yes Refl) | (Yes Refl) = p
    normDisj_isComplete {r=(Cat r s)} {s=(Cat r u)} p           | (Yes Refl) | (No _)     = p
  normDisj_isComplete {r=(Cat r s)} {s=(Cat t u)} p             | (No _) = p
normDisj_isComplete {r=(Cat _ _)}  {s=(Disj _ _)} p                     = p
normDisj_isComplete {r=(Cat _ _)}  {s=(Conj _ _)} p                     = p
normDisj_isComplete {r=(Cat _ _)}  {s=(Star _)} p                       = p
normDisj_isComplete {r=(Disj _ _)} {s=Null}       (InDisjL p)           = p
normDisj_isComplete {r=(Disj _ _)} {s=Null}       (InDisjR p)           = absurd $ nullMatchesAny_contra p
normDisj_isComplete {r=(Disj _ _)} {s=Empty}      (InDisjL (InDisjL p)) = InDisjL p
normDisj_isComplete {r=(Disj _ _)} {s=Empty}      (InDisjL (InDisjR p)) = InDisjR (InDisjL p)
normDisj_isComplete {r=(Disj _ _)} {s=Empty}      (InDisjR p)           = InDisjR (InDisjR p)
normDisj_isComplete {r=(Disj _ _)} {s=(Lit _)}    (InDisjL (InDisjL p)) = InDisjL p
normDisj_isComplete {r=(Disj _ _)} {s=(Lit _)}    (InDisjL (InDisjR p)) = InDisjR (InDisjL p)
normDisj_isComplete {r=(Disj _ _)} {s=(Lit _)}    (InDisjR p)           = InDisjR (InDisjR p)
normDisj_isComplete {r=(Disj _ _)} {s=(Cat _ _)}  (InDisjL (InDisjL p)) = InDisjL p
normDisj_isComplete {r=(Disj _ _)} {s=(Cat _ _)}  (InDisjL (InDisjR p)) = InDisjR (InDisjL p)
normDisj_isComplete {r=(Disj _ _)} {s=(Cat _ _)}  (InDisjR p)           = InDisjR (InDisjR p)
normDisj_isComplete {r=(Disj r s)} {s=(Disj t u)} p with (decEq r t)
  normDisj_isComplete {r=(Disj r s)} {s=(Disj r u)} p                       | (Yes Refl) with (decEq s u)
    normDisj_isComplete {r=(Disj r s)} {s=(Disj r s)} (InDisjL p)             | (Yes Refl) | (Yes Refl) = p
    normDisj_isComplete {r=(Disj r s)} {s=(Disj r s)} (InDisjR p)             | (Yes Refl) | (Yes Refl) = p
    normDisj_isComplete {r=(Disj r s)} {s=(Disj r u)} (InDisjL (InDisjL p)) | (Yes Refl) | (No _)       = InDisjL p
    normDisj_isComplete {r=(Disj r s)} {s=(Disj r u)} (InDisjL (InDisjR p)) | (Yes Refl) | (No _)       = InDisjR (InDisjL p)
    normDisj_isComplete {r=(Disj r s)} {s=(Disj r u)} (InDisjR p)             | (Yes Refl) | (No _)     = InDisjR (InDisjR p)
  normDisj_isComplete {r=(Disj r s)} {s=(Disj t u)} (InDisjL (InDisjL p))   | (No _)                    = InDisjL p
  normDisj_isComplete {r=(Disj r s)} {s=(Disj t u)} (InDisjL (InDisjR p))   | (No _)                    = InDisjR (InDisjL p)
  normDisj_isComplete {r=(Disj r s)} {s=(Disj t u)} (InDisjR p)               | (No _)                  = InDisjR (InDisjR p)
normDisj_isComplete {r=(Disj _ _)} {s=(Conj _ _)} (InDisjL (InDisjL p)) = InDisjL p
normDisj_isComplete {r=(Disj _ _)} {s=(Conj _ _)} (InDisjL (InDisjR p)) = InDisjR (InDisjL p)
normDisj_isComplete {r=(Disj _ _)} {s=(Conj _ _)} (InDisjR p)           = InDisjR (InDisjR p)
normDisj_isComplete {r=(Disj _ _)} {s=(Star _)}   (InDisjL (InDisjL p)) = InDisjL p
normDisj_isComplete {r=(Disj _ _)} {s=(Star _)}   (InDisjL (InDisjR p)) = InDisjR (InDisjL p)
normDisj_isComplete {r=(Disj _ _)} {s=(Star _)}   (InDisjR p)           = InDisjR (InDisjR p)
normDisj_isComplete {r=(Conj _ _)} {s=Null}       (InDisjL p)           = p
normDisj_isComplete {r=(Conj _ _)} {s=Null}       (InDisjR p)           = absurd $ nullMatchesAny_contra p
normDisj_isComplete {r=(Conj _ _)} {s=Empty}      p                     = p
normDisj_isComplete {r=(Conj _ _)} {s=(Lit _)}    p                     = p
normDisj_isComplete {r=(Conj _ _)} {s=(Cat _ _)}  p                     = p
normDisj_isComplete {r=(Conj _ _)} {s=(Disj _ _)} p                     = p
normDisj_isComplete {r=(Conj r s)} {s=(Conj t u)} p with (decEq r t)
  normDisj_isComplete {r=(Conj r s)} {s=(Conj r u)} p | (Yes Refl) with (decEq s u)
    normDisj_isComplete {r=(Conj r s)} {s=(Conj r s)} (InDisjL p) | (Yes Refl) | (Yes Refl) = p
    normDisj_isComplete {r=(Conj r s)} {s=(Conj r s)} (InDisjR p) | (Yes Refl) | (Yes Refl) = p
    normDisj_isComplete {r=(Conj r s)} {s=(Conj r u)} p           | (Yes Refl) | (No _)     = p
  normDisj_isComplete {r=(Conj r s)} {s=(Conj t u)} p | (No _)                              = p
normDisj_isComplete {r=(Conj _ _)} {s=(Star _)}   p                     = p
normDisj_isComplete {r=(Star _)} {s=Null}         (InDisjL p)           = p
normDisj_isComplete {r=(Star _)} {s=Null}         (InDisjR p)           = absurd $ nullMatchesAny_contra p
normDisj_isComplete {r=(Star _)} {s=Empty}        p                     = p
normDisj_isComplete {r=(Star _)} {s=(Lit _)}      p                     = p
normDisj_isComplete {r=(Star _)} {s=(Cat _ _)}    p                     = p
normDisj_isComplete {r=(Star _)} {s=(Disj _ _)}   p                     = p
normDisj_isComplete {r=(Star _)} {s=(Conj _ _)}   p                     = p
normDisj_isComplete {r=(Star r)} {s=(Star s)} p with (decEq r s)
  normDisj_isComplete {r=(Star r)} {s=(Star r)}   (InDisjL p) | (Yes Refl) = p
  normDisj_isComplete {r=(Star r)} {s=(Star r)}   (InDisjR p) | (Yes Refl) = p
  normDisj_isComplete {r=(Star r)} {s=(Star s)}   p           | (No _)     = p
