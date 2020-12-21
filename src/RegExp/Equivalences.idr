||| Defines functions to use in place of `RegExp`'s data constructors, in order to create
||| regular expressions which are "normalized" to a canonical form as much as possible. This adds
||| some compile-time complexity but results in smaller DFAs for testing language membership.
module RegExp.Equivalences

import Data.List
import Decidable.Equality

import public RegExp.Types

%default total

||| Constructs a "normalized" `Cat`, which applies the following rules:
|||   - ∅ · r ≈ ∅
|||   - r · ∅ ≈ ∅
|||   - ε · r ≈ r
|||   - r · ε ≈ r
|||   - (r · s) · t ≈ r · (s · t)
export
normCat : DecEq a => RegExp a -> RegExp a -> RegExp a
normCat Null      _     = Null
normCat _         Null  = Null
normCat Empty     r     = r
normCat r         Empty = r
normCat (Cat r s) t     = Cat r (Cat s t)
normCat r         s     = Cat r s

||| Constructs a "normalized" `Disj`, which applies the following rules:
|||
|||   - ∅ + r ≈ r
|||   - r + r ≈ r
|||   - (r + s) + t ≈ r + (s + t)
|||
||| Note that the remaining equivalence (symmetry) is not captured:
|||
|||   - r + s ≈ s + r
export
normDisj : DecEq a => RegExp a -> RegExp a -> RegExp a
normDisj Null r    = r
normDisj r    Null = r
normDisj r s with (decEq r s)
  normDisj r          r | (Yes Refl) = r
  normDisj (Disj r s) t | (No _)     = Disj r (Disj s t)
  normDisj r          s | (No _)     = Disj r s

||| Constructs a "normalized" `Conj`, which applies the following rules:
|||   - ∅ & r ≈ ∅
|||   - r & r ≈ r
|||   - (r & s) & t ≈ r & (s & t)
|||
||| Note that the remaining equivalence (symmetry) is not captured:
|||
|||   - r & s ≈ s & r
export
normConj : DecEq a => RegExp a -> RegExp a -> RegExp a
normConj Null _    = Null
normConj _    Null = Null
normConj r s with (decEq r s)
  normConj r r          | (Yes Refl) = r
  normConj (Conj r s) t | (No _)     = Conj r (Conj s t)
  normConj r s          | (No _)     = Conj r s

||| Proof (by exhaustion) that `normCat` is sound.
export
normCat_isSound : DecEq a =>
                  {xs : List a} ->
                  {r : RegExp a} ->
                  {s : RegExp a} ->
                  InRegExp (normCat r s) xs ->
                  InRegExp (Cat r s) xs
normCat_isSound      {r=Null}       {s}            p = absurd p
normCat_isSound      {r=Empty}      {s=Null}       p = absurd p
normCat_isSound      {r=Empty}      {s=Empty}      p = InCat Refl InEmpty p
normCat_isSound      {r=Empty}      {s=(Lit _)}    p = InCat Refl InEmpty p
normCat_isSound      {r=Empty}      {s=(Cat _ _)}  p = InCat Refl InEmpty p
normCat_isSound      {r=Empty}      {s=(Disj _ _)} p = InCat Refl InEmpty p
normCat_isSound      {r=Empty}      {s=(Conj _ _)} p = InCat Refl InEmpty p
normCat_isSound      {r=Empty}      {s=(Star _)}   p = InCat Refl InEmpty p
normCat_isSound      {r=(Lit _)}    {s=Null}       p = absurd p
normCat_isSound {xs} {r=(Lit _)}    {s=Empty}      p = InCat (sym $ appendNilRightNeutral xs) p InEmpty
normCat_isSound      {r=(Lit _)}    {s=(Lit _)}    p = p
normCat_isSound      {r=(Lit _)}    {s=(Cat _ _)}  p = p
normCat_isSound      {r=(Lit _)}    {s=(Disj _ _)} p = p
normCat_isSound      {r=(Lit _)}    {s=(Conj _ _)} p = p
normCat_isSound      {r=(Lit _)}    {s=(Star _)}   p = p
normCat_isSound      {r=(Cat _ _)}  {s=Null}       p = absurd p
normCat_isSound {xs} {r=(Cat _ _)}  {s=Empty}      p = InCat (sym $ appendNilRightNeutral xs) p InEmpty
normCat_isSound {xs=xs++(ys++zs)} {r=(Cat _ _)} {s=(Lit _)} (InCat {xs} {ys=ys++zs} Refl pr (InCat {xs=ys} {ys=zs} Refl ps pl)) =
  InCat (appendAssociative xs ys zs) (InCat Refl pr ps) pl
normCat_isSound {xs=xs++(ys++zs)} {r=(Cat _ _)} {s=(Cat _ _)} (InCat {xs} {ys=ys++zs} Refl pr (InCat {xs=ys} {ys=zs} Refl ps pl)) =
  InCat (appendAssociative xs ys zs) (InCat Refl pr ps) pl
normCat_isSound {xs=xs++(ys++zs)} {r=(Cat _ _)} {s=(Disj _ _)} (InCat {xs} {ys=ys++zs} Refl pr (InCat {xs=ys} {ys=zs} Refl ps pl)) =
  InCat (appendAssociative xs ys zs) (InCat Refl pr ps) pl
normCat_isSound {xs=xs++(ys++zs)} {r=(Cat _ _)} {s=(Conj _ _)} (InCat {xs} {ys=ys++zs} Refl pr (InCat {xs=ys} {ys=zs} Refl ps pl)) =
  InCat (appendAssociative xs ys zs) (InCat Refl pr ps) pl
normCat_isSound {xs=xs++(ys++zs)} {r=(Cat _ _)} {s=(Star _)} (InCat {xs} {ys=ys++zs} Refl pr (InCat {xs=ys} {ys=zs} Refl ps pl)) =
  InCat (appendAssociative xs ys zs) (InCat Refl pr ps) pl
normCat_isSound      {r=(Disj _ _)} {s=Null}       p = absurd p
normCat_isSound {xs} {r=(Disj _ _)} {s=Empty}      p = InCat (sym $ appendNilRightNeutral xs) p InEmpty
normCat_isSound      {r=(Disj _ _)} {s=(Lit z)}    p = p
normCat_isSound      {r=(Disj _ _)} {s=(Cat z w)}  p = p
normCat_isSound      {r=(Disj _ _)} {s=(Disj z w)} p = p
normCat_isSound      {r=(Disj _ _)} {s=(Conj z w)} p = p
normCat_isSound      {r=(Disj _ _)} {s=(Star z)}   p = p
normCat_isSound      {r=(Conj _ _)} {s=Null}       p = absurd p
normCat_isSound {xs} {r=(Conj _ _)} {s=Empty}      p = InCat (sym $ appendNilRightNeutral xs) p InEmpty
normCat_isSound      {r=(Conj _ _)} {s=(Lit z)}    p = p
normCat_isSound      {r=(Conj _ _)} {s=(Cat z w)}  p = p
normCat_isSound      {r=(Conj _ _)} {s=(Disj z w)} p = p
normCat_isSound      {r=(Conj _ _)} {s=(Conj z w)} p = p
normCat_isSound      {r=(Conj _ _)} {s=(Star z)}   p = p
normCat_isSound      {r=(Star _)}   {s=Null}       p = absurd p
normCat_isSound {xs} {r=(Star _)}   {s=Empty}      p = InCat (sym $ appendNilRightNeutral xs) p InEmpty
normCat_isSound      {r=(Star _)}   {s=(Lit y)}    p = p
normCat_isSound      {r=(Star _)}   {s=(Cat y z)}  p = p
normCat_isSound      {r=(Star _)}   {s=(Disj y z)} p = p
normCat_isSound      {r=(Star _)}   {s=(Conj y z)} p = p
normCat_isSound      {r=(Star _)}   {s=(Star y)}   p = p

||| Proof (by exhaustion) that `normCat` is complete.
export
normCat_isComplete : DecEq a =>
                     {xs : List a} ->
                     {r : RegExp a} ->
                     {s : RegExp a} ->
                     InRegExp (Cat r s) xs ->
                     InRegExp (normCat r s) xs
normCat_isComplete {r=Null}                      (InCat _ pr _) = absurd pr
normCat_isComplete                {s=Null}       (InCat _ _ ps) = absurd ps
normCat_isComplete {r=Empty}      {s=Empty}      (InCat pCat InEmpty ps) = rewrite pCat in ps
normCat_isComplete {r=Empty}      {s=(Lit _)}    (InCat pCat InEmpty ps) = rewrite pCat in ps
normCat_isComplete {r=Empty}      {s=(Cat _ _)}  (InCat pCat InEmpty ps) = rewrite pCat in ps
normCat_isComplete {r=Empty}      {s=(Disj _ _)} (InCat pCat InEmpty ps) = rewrite pCat in ps
normCat_isComplete {r=Empty}      {s=(Conj _ _)} (InCat pCat InEmpty ps) = rewrite pCat in ps
normCat_isComplete {r=Empty}      {s=(Star _)}   (InCat pCat InEmpty ps) = rewrite pCat in ps
normCat_isComplete {r=(Lit _)}    {s=Empty}      (InCat {xs} Refl pr InEmpty) = rewrite (appendNilRightNeutral xs) in pr
normCat_isComplete {r=(Lit _)}    {s=(Lit _)}    p = p
normCat_isComplete {r=(Lit _)}    {s=(Cat _ _)}  p = p
normCat_isComplete {r=(Lit _)}    {s=(Disj _ _)} p = p
normCat_isComplete {r=(Lit _)}    {s=(Conj _ _)} p = p
normCat_isComplete {r=(Lit _)}    {s=(Star _)}   p = p
normCat_isComplete {r=(Cat _ _)}  {s=Empty} (InCat {xs} Refl pr InEmpty) = rewrite (appendNilRightNeutral xs) in pr
normCat_isComplete {xs=(xs'++ys)++[x]} {r=(Cat _ _)} {s=(Lit x)} (InCat {xs=xs'++ys} {ys=[x]} Refl (InCat {xs=xs'} {ys} Refl pr ps) InLit) =
  InCat (sym $ appendAssociative xs' ys [x]) pr (InCat Refl ps InLit)
normCat_isComplete {xs=(xs'++ys)++zs} {r=(Cat _ _)} {s=(Cat _ _)} (InCat {xs=xs'++ys} {ys=zs} Refl (InCat {xs=xs'} {ys} Refl pr ps) pt) =
  InCat (sym $ appendAssociative xs' ys zs) pr (InCat Refl ps pt)
normCat_isComplete {xs=(xs'++ys)++zs} {r=(Cat _ _)} {s=(Disj _ _)} (InCat {xs=xs'++ys} {ys=zs} Refl (InCat {xs=xs'} {ys} Refl pr ps) pt) =
  InCat (sym $ appendAssociative xs' ys zs) pr (InCat Refl ps pt)
normCat_isComplete {xs=(xs'++ys)++zs} {r=(Cat _ _)} {s=(Conj _ _)} (InCat {xs=xs'++ys} {ys=zs} Refl (InCat {xs=xs'} {ys} Refl pr ps) pt) =
  InCat (sym $ appendAssociative xs' ys zs) pr (InCat Refl ps pt)
normCat_isComplete {xs=(xs'++ys)++zs} {r=(Cat _ _)} {s=(Star _)} (InCat {xs=xs'++ys} {ys=zs} Refl (InCat {xs=xs'} {ys} Refl pr ps) pt) =
  InCat (sym $ appendAssociative xs' ys zs) pr (InCat Refl ps pt)
normCat_isComplete {r=(Disj _ _)} {s=Empty}      (InCat {xs} Refl pr InEmpty) = rewrite (appendNilRightNeutral xs) in pr
normCat_isComplete {r=(Disj _ _)} {s=(Lit _)}    p = p
normCat_isComplete {r=(Disj _ _)} {s=(Cat _ _)}  p = p
normCat_isComplete {r=(Disj _ _)} {s=(Disj _ _)} p = p
normCat_isComplete {r=(Disj _ _)} {s=(Conj _ _)} p = p
normCat_isComplete {r=(Disj _ _)} {s=(Star _)}   p = p
normCat_isComplete {r=(Conj _ _)} {s=Empty}      (InCat {xs} Refl pr InEmpty) = rewrite (appendNilRightNeutral xs) in pr
normCat_isComplete {r=(Conj _ _)} {s=(Lit _)}    p = p
normCat_isComplete {r=(Conj _ _)} {s=(Cat _ _)}  p = p
normCat_isComplete {r=(Conj _ _)} {s=(Disj _ _)} p = p
normCat_isComplete {r=(Conj _ _)} {s=(Conj _ _)} p = p
normCat_isComplete {r=(Conj _ _)} {s=(Star _)}   p = p
normCat_isComplete {r=(Star _)}   {s=Empty}      (InCat {xs} Refl pr InEmpty) = rewrite (appendNilRightNeutral xs) in pr
normCat_isComplete {r=(Star _)}   {s=(Lit _)}    p = p
normCat_isComplete {r=(Star _)}   {s=(Cat _ _)}  p = p
normCat_isComplete {r=(Star _)}   {s=(Disj _ _)} p = p
normCat_isComplete {r=(Star _)}   {s=(Conj _ _)} p = p
normCat_isComplete {r=(Star _)}   {s=(Star _)}   p = p

||| Proof (by exhaustion) that `normDisj` is sound.
export
normDisj_isSound : DecEq a =>
                   {xs : List a} ->
                   {r : RegExp a} ->
                   {s : RegExp a} ->
                   InRegExp (normDisj r s) xs ->
                   InRegExp (Disj r s) xs
normDisj_isSound {r=Null}                      p                     = InDisjR p
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
normDisj_isComplete {r=Null}                      (InDisjL p)           = absurd p
normDisj_isComplete {r=Null}                      (InDisjR p)           = p
normDisj_isComplete {r=Empty}      {s=Null}       (InDisjL p)           = p
normDisj_isComplete {r=Empty}      {s=Null}       (InDisjR p)           = absurd p
normDisj_isComplete {r=Empty}      {s=Empty}      (InDisjL p)           = InDisjL p
normDisj_isComplete {r=Empty}      {s=Empty}      (InDisjR p)           = InDisjR p
normDisj_isComplete {r=Empty}      {s=(Lit _)}    p                     = p
normDisj_isComplete {r=Empty}      {s=(Cat _ _)}  p                     = p
normDisj_isComplete {r=Empty}      {s=(Disj _ _)} p                     = p
normDisj_isComplete {r=Empty}      {s=(Conj _ _)} p                     = p
normDisj_isComplete {r=Empty}      {s=(Star _)}   p                     = p
normDisj_isComplete {r=(Lit _)}    {s=Null}       (InDisjL p)           = p
normDisj_isComplete {r=(Lit _)}    {s=Null}       (InDisjR p)           = absurd p
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
normDisj_isComplete {r=(Cat _ _)}  {s=Null} (InDisjR p)                 = absurd p
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
normDisj_isComplete {r=(Disj _ _)} {s=Null}       (InDisjR p)           = absurd p
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
normDisj_isComplete {r=(Conj _ _)} {s=Null}       (InDisjR p)           = absurd p
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
normDisj_isComplete {r=(Star _)} {s=Null}         (InDisjR p)           = absurd p
normDisj_isComplete {r=(Star _)} {s=Empty}        p                     = p
normDisj_isComplete {r=(Star _)} {s=(Lit _)}      p                     = p
normDisj_isComplete {r=(Star _)} {s=(Cat _ _)}    p                     = p
normDisj_isComplete {r=(Star _)} {s=(Disj _ _)}   p                     = p
normDisj_isComplete {r=(Star _)} {s=(Conj _ _)}   p                     = p
normDisj_isComplete {r=(Star r)} {s=(Star s)} p with (decEq r s)
  normDisj_isComplete {r=(Star r)} {s=(Star r)}   (InDisjL p) | (Yes Refl) = p
  normDisj_isComplete {r=(Star r)} {s=(Star r)}   (InDisjR p) | (Yes Refl) = p
  normDisj_isComplete {r=(Star r)} {s=(Star s)}   p           | (No _)     = p

||| Proof (by exhaustion) that `normConj` is sound.
export
normConj_isSound : DecEq a =>
                   {xs : List a} ->
                   {r : RegExp a} ->
                   {s : RegExp a} ->
                   InRegExp (normConj r s) xs ->
                   InRegExp (Conj r s) xs
normConj_isSound {r=Null}       {s}       p = absurd p
normConj_isSound {r=Empty}      {s=Null}       p = absurd p
normConj_isSound {r=Empty}      {s=Empty}      p = p
normConj_isSound {r=Empty}      {s=(Lit _)}    p = p
normConj_isSound {r=Empty}      {s=(Cat _ _)}  p = p
normConj_isSound {r=Empty}      {s=(Disj _ _)} p = p
normConj_isSound {r=Empty}      {s=(Conj _ _)} p = p
normConj_isSound {r=Empty}      {s=(Star _)}   p = p
normConj_isSound {r=(Lit _)}    {s=Null}       p = absurd p
normConj_isSound {r=(Lit _)}    {s=Empty}      p = p
normConj_isSound {r=(Lit x)}    {s=(Lit y)}    p with (decEq x y)
  normConj_isSound {r=(Lit x)}    {s=(Lit x)}    p | (Yes Refl) = InConj p p
  normConj_isSound {r=(Lit x)}    {s=(Lit y)}    p | (No _)     = p
normConj_isSound {r=(Lit _)}    {s=(Cat _ _)}  p = p
normConj_isSound {r=(Lit _)}    {s=(Disj _ _)} p = p
normConj_isSound {r=(Lit _)}    {s=(Conj _ _)} p = p
normConj_isSound {r=(Lit _)}    {s=(Star _)}   p = p
normConj_isSound {r=(Cat _ _)}  {s=Null}       p = absurd p
normConj_isSound {r=(Cat _ _)}  {s=Empty}      p = p
normConj_isSound {r=(Cat _ _)}  {s=(Lit _)}    p = p
normConj_isSound {r=(Cat r s)}  {s=(Cat t u)}  p with (decEq r t)
  normConj_isSound {r=(Cat r s)} {s=(Cat r u)} p | (Yes Refl) with (decEq s u)
    normConj_isSound {r=(Cat r s)} {s=(Cat r s)} p | (Yes Refl) | (Yes Refl) = InConj p p
    normConj_isSound {r=(Cat r s)} {s=(Cat r u)} p | (Yes Refl) | (No _) = p
  normConj_isSound {r=(Cat r s)} {s=(Cat t u)} p | (No _) = p
normConj_isSound {r=(Cat _ _)}  {s=(Disj _ _)} p = p
normConj_isSound {r=(Cat _ _)}  {s=(Conj _ _)} p = p
normConj_isSound {r=(Cat _ _)}  {s=(Star _)}   p = p
normConj_isSound {r=(Disj _ _)} {s=Null}       p = absurd p
normConj_isSound {r=(Disj _ _)} {s=Empty}      p = p
normConj_isSound {r=(Disj _ _)} {s=(Lit _)}    p = p
normConj_isSound {r=(Disj _ _)} {s=(Cat _ _)}  p = p
normConj_isSound {r=(Disj r s)} {s=(Disj t u)} p with (decEq r t)
  normConj_isSound {r=(Disj r s)} {s=(Disj r u)} p | (Yes Refl) with (decEq s u)
    normConj_isSound {r=(Disj r s)} {s=(Disj r s)} p | (Yes Refl) | (Yes Refl) = InConj p p
    normConj_isSound {r=(Disj r s)} {s=(Disj r u)} p | (Yes Refl) | (No _) = p
  normConj_isSound {r=(Disj r s)} {s=(Disj t u)} p | (No _) = p
normConj_isSound {r=(Disj _ _)} {s=(Conj _ _)} p = p
normConj_isSound {r=(Disj _ _)} {s=(Star _)}   p = p
normConj_isSound {r=(Conj _ _)} {s=Null}       p = absurd p
normConj_isSound {r=(Conj _ _)} {s=Empty}      (InConj pr (InConj ps pt)) = InConj (InConj pr ps) pt
normConj_isSound {r=(Conj _ _)} {s=(Lit _)}    (InConj pr (InConj ps pt)) = InConj (InConj pr ps) pt
normConj_isSound {r=(Conj _ _)} {s=(Cat _ _)}  (InConj pr (InConj ps pt)) = InConj (InConj pr ps) pt
normConj_isSound {r=(Conj _ _)} {s=(Disj _ _)} (InConj pr (InConj ps pt)) = InConj (InConj pr ps) pt
normConj_isSound {r=(Conj r s)} {s=(Conj t u)} p with (decEq r t)
  normConj_isSound {r=(Conj r s)} {s=(Conj r u)} p | (Yes Refl) with (decEq s u)
    normConj_isSound {r=(Conj r s)} {s=(Conj r s)} p | (Yes Refl) | (Yes Refl) = InConj p p
    normConj_isSound {r=(Conj r s)} {s=(Conj r u)} (InConj _ (InConj ps (InConj pt pu))) | (Yes Refl) | (No _) =
      InConj (InConj pt ps) (InConj pt pu)
  normConj_isSound {r=(Conj r s)} {s=(Conj t u)} (InConj pr (InConj ps (InConj pt pu))) | (No _) =
    InConj (InConj pr ps) (InConj pt pu)
normConj_isSound {r=(Conj _ _)} {s=(Star _)}   (InConj pr (InConj ps pt)) = InConj (InConj pr ps) pt
normConj_isSound {r=(Star _)}   {s=Null}       p = absurd p
normConj_isSound {r=(Star _)}   {s=Empty}      p = p
normConj_isSound {r=(Star _)}   {s=(Lit _)}    p = p
normConj_isSound {r=(Star _)}   {s=(Cat _ _)}  p = p
normConj_isSound {r=(Star _)}   {s=(Disj _ _)} p = p
normConj_isSound {r=(Star _)}   {s=(Conj _ _)} p = p
normConj_isSound {r=(Star r)}   {s=(Star s)}   p with (decEq r s)
  normConj_isSound {r=(Star r)}   {s=(Star r)}   p | (Yes Refl) = InConj p p
  normConj_isSound {r=(Star r)}   {s=(Star s)}   p | (No _)     = p

||| Proof (by exhaustion) that `normCat` is complete.
export
normConj_isComplete : DecEq a =>
                      {xs : List a} ->
                      {r : RegExp a} ->
                      {s : RegExp a} ->
                      InRegExp (Conj r s) xs ->
                      InRegExp (normConj r s) xs
normConj_isComplete {r=Null}                      (InConj p _) = absurd p
normConj_isComplete                {s=Null}       (InConj _ p) = absurd p
normConj_isComplete {r=Empty}      {s=Empty}      p = p
normConj_isComplete {r=Empty}      {s=(Lit _)}    p = p
normConj_isComplete {r=Empty}      {s=(Cat _ _)}  p = p
normConj_isComplete {r=Empty}      {s=(Disj _ _)} p = p
normConj_isComplete {r=Empty}      {s=(Conj _ _)} p = p
normConj_isComplete {r=Empty}      {s=(Star _)}   p = p
normConj_isComplete {r=(Lit _)}    {s=Empty}      p = p
normConj_isComplete {r=(Lit x)}    {s=(Lit y)}    p with (decEq x y)
  normConj_isComplete {r=(Lit x)}  {s=(Lit x)}    (InConj p _) | Yes Refl = p
  normConj_isComplete {r=(Lit x)}  {s=(Lit y)}    p            | No _     = p
normConj_isComplete {r=(Lit _)}    {s=(Cat _ _)}  p = p
normConj_isComplete {r=(Lit _)}    {s=(Disj _ _)} p = p
normConj_isComplete {r=(Lit _)}    {s=(Conj _ _)} p = p
normConj_isComplete {r=(Lit _)}    {s=(Star _)}   p = p
normConj_isComplete {r=(Cat _ _)}  {s=Empty}      p = p
normConj_isComplete {r=(Cat _ _)}  {s=(Lit _)}    p = p
normConj_isComplete {r=(Cat r s)}   {s=(Cat t u)} p with (decEq (Cat r s) (Cat t u))
  normConj_isComplete {r=(Cat r s)} {s=(Cat r s)} (InConj p _) | Yes Refl = p
  normConj_isComplete {r=(Cat r s)} {s=(Cat t u)} p            | No _     = p
normConj_isComplete {r=(Cat _ _)}  {s=(Disj _ _)} p = p
normConj_isComplete {r=(Cat _ _)}  {s=(Conj _ _)} p = p
normConj_isComplete {r=(Cat _ _)}  {s=(Star _)}   p = p
normConj_isComplete {r=(Disj _ _)} {s=Empty}      p = p
normConj_isComplete {r=(Disj _ _)} {s=(Lit _)}    p = p
normConj_isComplete {r=(Disj _ _)} {s=(Cat _ _)}  p = p
normConj_isComplete {r=(Disj r s)}   {s=(Disj t u)} p with (decEq (Disj r s) (Disj t u))
  normConj_isComplete {r=(Disj r s)} {s=(Disj r s)} (InConj p _) | Yes Refl = p
  normConj_isComplete {r=(Disj r s)} {s=(Disj t u)} p            | No _     = p
normConj_isComplete {r=(Disj _ _)} {s=(Conj _ _)} p = p
normConj_isComplete {r=(Disj _ _)} {s=(Star _)}   p = p
normConj_isComplete {r=(Conj _ _)} {s=Empty}      (InConj (InConj pr ps) pt) = InConj pr (InConj ps pt)
normConj_isComplete {r=(Conj _ _)} {s=(Lit _)}    (InConj (InConj pr ps) pt) = InConj pr (InConj ps pt)
normConj_isComplete {r=(Conj _ _)} {s=(Cat _ _)}  (InConj (InConj pr ps) pt) = InConj pr (InConj ps pt)
normConj_isComplete {r=(Conj _ _)} {s=(Disj _ _)} (InConj (InConj pr ps) pt) = InConj pr (InConj ps pt)
normConj_isComplete {r=(Conj r s)} {s=(Conj t u)} p with (decEq (Conj r s) (Conj t u))
  normConj_isComplete {r=(Conj r s)} {s=(Conj r s)} (InConj p _)                           | Yes Refl = p
  normConj_isComplete {r=(Conj r s)} {s=(Conj t u)} (InConj (InConj pr ps) (InConj pt pu)) | No _     =
    InConj pr (InConj ps (InConj pt pu))
normConj_isComplete {r=(Conj _ _)} {s=(Star _)}   (InConj (InConj pr ps) pt) = InConj pr (InConj ps pt)
normConj_isComplete {r=(Star _)}   {s=Empty}      p = p
normConj_isComplete {r=(Star _)}   {s=(Lit _)}    p = p
normConj_isComplete {r=(Star _)}   {s=(Cat _ _)}  p = p
normConj_isComplete {r=(Star _)}   {s=(Disj _ _)} p = p
normConj_isComplete {r=(Star _)}   {s=(Conj _ _)} p = p
normConj_isComplete {r=(Star r)}   {s=(Star s)}   p with (decEq r s)
  normConj_isComplete {r=(Star r)} {s=(Star r)}   (InConj p _) | Yes Refl = p
  normConj_isComplete {r=(Star r)} {s=(Star s)}   p            | No _     = p
