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
-- TODO enable after Comp is implemented
-- normDisj (Comp Null) r = Comp Null
-- normDisj r (Comp Null) = Comp Null
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
normDisj_isSound {r=Null}       {s}            p                             = InDisjR Null s p
normDisj_isSound {r=Empty}      {s=Null}       p                             = InDisjL Empty Null p
normDisj_isSound {r=Empty}      {s=Empty}      p                             = InDisjL Empty Empty p
normDisj_isSound {r=Empty}      {s=(Lit x)}    p                             = p
normDisj_isSound {r=Empty}      {s=(Disj x y)} p                             = p
normDisj_isSound {r=(Lit x)}    {s=Null}       p                             = InDisjL (Lit x) Null p
normDisj_isSound {r=(Lit x)}    {s=Empty}      p                             = p
normDisj_isSound {r=(Lit x)}    {s=(Lit y)}    p with (decEq x y)
  normDisj_isSound {r=(Lit x)} {s=(Lit x)} p | (Yes Refl)  = InDisjL (Lit x) (Lit x) p
  normDisj_isSound {r=(Lit x)} {s=(Lit y)} p | (No contra) = p
normDisj_isSound {r=(Lit x)}    {s=(Disj r s)} p                             = p
normDisj_isSound {r=(Disj r s)} {s=Null}       p                             = InDisjL (Disj r s) Null p
normDisj_isSound {r=(Disj r s)} {s=Empty}      (InDisjL _ _ p)               = InDisjL (Disj r s) Empty (InDisjL r s p)
normDisj_isSound {r=(Disj r s)} {s=Empty}      (InDisjR _ _ (InDisjL _ _ p)) = InDisjL (Disj r s) Empty (InDisjR r s p)
normDisj_isSound {r=(Disj r s)} {s=Empty}      (InDisjR _ _ (InDisjR _ _ p)) = InDisjR (Disj r s) Empty p
normDisj_isSound {r=(Disj r s)} {s=(Lit x)}    (InDisjL _ _ p)               = InDisjL (Disj r s) (Lit x) (InDisjL r s p)
normDisj_isSound {r=(Disj r s)} {s=(Lit x)}    (InDisjR _ _ (InDisjL _ _ p)) = InDisjL (Disj r s) (Lit x) (InDisjR r s p)
normDisj_isSound {r=(Disj r s)} {s=(Lit x)}    (InDisjR _ _ (InDisjR _ _ p)) = InDisjR (Disj r s) (Lit x) p
normDisj_isSound {r=(Disj r s)} {s=(Disj t u)} p with (decEq r t)
  normDisj_isSound {r=(Disj r s)} {s=(Disj r u)} p                             | (Yes Refl) with (decEq s u)
    normDisj_isSound {r=(Disj r s)} {s=(Disj r s)} p                             | (Yes Refl) | (Yes Refl) = InDisjL (Disj r s) (Disj r s) p
    normDisj_isSound {r=(Disj r s)} {s=(Disj r u)} (InDisjL _ _ p)               | (Yes Refl) | (No _)     = InDisjL (Disj r s) (Disj r u) (InDisjL r s p)
    normDisj_isSound {r=(Disj r s)} {s=(Disj r u)} (InDisjR _ _ (InDisjL _ _ p)) | (Yes Refl) | (No _)     = InDisjL (Disj r s) (Disj r u) (InDisjR r s p)
    normDisj_isSound {r=(Disj r s)} {s=(Disj r u)} (InDisjR _ _ (InDisjR _ _ p)) | (Yes Refl) | (No _)     = InDisjR (Disj r s) (Disj r u) p
  normDisj_isSound {r=(Disj r s)} {s=(Disj t u)} (InDisjL _ _ p)               | (No _) = InDisjL (Disj r s) (Disj t u) (InDisjL r s p)
  normDisj_isSound {r=(Disj r s)} {s=(Disj t u)} (InDisjR _ _ (InDisjL _ _ p)) | (No _) = InDisjL (Disj r s) (Disj t u) (InDisjR r s p)
  normDisj_isSound {r=(Disj r s)} {s=(Disj t u)} (InDisjR _ _ (InDisjR _ _ p)) | (No _) = InDisjR (Disj r s) (Disj t u) p

||| Proof (by exhaustion) that `normDisj` is complete.
export
normDisj_isComplete : DecEq a =>
                      {xs : List a} ->
                      {r : RegExp a} ->
                      {s : RegExp a} ->
                      InRegExp (Disj r s) xs ->
                      InRegExp (normDisj r s) xs
normDisj_isComplete {r=Null}       {s=_}          (InDisjL _ _ p)               = absurd $ nullMatchesAny_contra p
normDisj_isComplete {r=Null}       {s=_}          (InDisjR _ _ p)               = p
normDisj_isComplete {r=Empty}      {s=Null}       (InDisjL _ _ p)               = p
normDisj_isComplete {r=Empty}      {s=Null}       (InDisjR _ _ p)               = absurd $ nullMatchesAny_contra p
normDisj_isComplete {r=Empty}      {s=Empty}      (InDisjL _ _ p)               = p
normDisj_isComplete {r=Empty}      {s=Empty}      (InDisjR _ _ p)               = p
normDisj_isComplete {r=Empty}      {s=(Lit _)}    p                             = p
normDisj_isComplete {r=Empty}      {s=(Disj _ _)} p                             = p
normDisj_isComplete {r=(Lit _)}    {s=Null}       (InDisjL _ _ p)               = p
normDisj_isComplete {r=(Lit _)}    {s=Null}       (InDisjR _ _ p)               = absurd $ nullMatchesAny_contra p
normDisj_isComplete {r=(Lit _)}    {s=Empty}      p                             = p
normDisj_isComplete {r=(Lit x)}    {s=(Lit y)} p with (decEq x y)
  normDisj_isComplete {r=(Lit x)} {s=(Lit x)} (InDisjL _ _ p) | (Yes Refl) = p
  normDisj_isComplete {r=(Lit x)} {s=(Lit x)} (InDisjR _ _ p) | (Yes Refl) = p
  normDisj_isComplete {r=(Lit x)} {s=(Lit y)} p               | (No _)     = p
normDisj_isComplete {r=(Lit x)}    {s=(Disj r s)} p = p
normDisj_isComplete {r=(Disj r s)} {s=Null}       (InDisjL _ _ p)               = p
normDisj_isComplete {r=(Disj r s)} {s=Null}       (InDisjR _ _ p)               = absurd $ nullMatchesAny_contra p
normDisj_isComplete {r=(Disj r s)} {s=Empty}      (InDisjL _ _ (InDisjL _ _ p)) = InDisjL r (Disj s Empty) p
normDisj_isComplete {r=(Disj r s)} {s=Empty}      (InDisjL _ _ (InDisjR _ _ p)) = InDisjR r (Disj s Empty) (InDisjL s Empty p)
normDisj_isComplete {r=(Disj r s)} {s=Empty}      (InDisjR _ _ p)               = InDisjR r (Disj s Empty) (InDisjR s Empty p)
normDisj_isComplete {r=(Disj r s)} {s=(Lit _)}    (InDisjL _ _ (InDisjL _ _ p)) = InDisjL r (Disj s (Lit _)) p
normDisj_isComplete {r=(Disj r s)} {s=(Lit _)}    (InDisjL _ _ (InDisjR _ _ p)) = InDisjR r (Disj s (Lit _)) (InDisjL s (Lit _) p)
normDisj_isComplete {r=(Disj r s)} {s=(Lit _)}    (InDisjR _ _ p)               = InDisjR r (Disj s (Lit _)) (InDisjR s (Lit _) p)
normDisj_isComplete {r=(Disj r s)} {s=(Disj t u)} p with (decEq r t)
  normDisj_isComplete {r=(Disj r s)} {s=(Disj r u)} p                             | (Yes Refl) with (decEq s u)
    normDisj_isComplete {r=(Disj r s)} {s=(Disj r s)} (InDisjL _ _ p)               | (Yes Refl) | (Yes Refl) = p
    normDisj_isComplete {r=(Disj r s)} {s=(Disj r s)} (InDisjR _ _ p)               | (Yes Refl) | (Yes Refl) = p
    normDisj_isComplete {r=(Disj r s)} {s=(Disj r u)} (InDisjL _ _ (InDisjL _ _ p)) | (Yes Refl) | (No _)     = InDisjL r (Disj s (Disj r u)) p
    normDisj_isComplete {r=(Disj r s)} {s=(Disj r u)} (InDisjL _ _ (InDisjR _ _ p)) | (Yes Refl) | (No _)     = InDisjR r (Disj s (Disj r u)) (InDisjL s (Disj r u) p)
    normDisj_isComplete {r=(Disj r s)} {s=(Disj r u)} (InDisjR _ _ p)               | (Yes Refl) | (No _)     = InDisjR r (Disj s (Disj r u)) (InDisjR s (Disj r u) p)
  normDisj_isComplete {r=(Disj r s)} {s=(Disj t u)} (InDisjL _ _ (InDisjL _ _ p)) | (No _) = InDisjL r (Disj s (Disj t u)) p
  normDisj_isComplete {r=(Disj r s)} {s=(Disj t u)} (InDisjL _ _ (InDisjR _ _ p)) | (No _) = InDisjR r (Disj s (Disj t u)) (InDisjL s (Disj t u) p)
  normDisj_isComplete {r=(Disj r s)} {s=(Disj t u)} (InDisjR _ _ p)               | (No _) = InDisjR r (Disj s (Disj t u)) (InDisjR s (Disj t u) p)
