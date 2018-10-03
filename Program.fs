// This file is part of Presburger-fs.
//
// Presburger-fs is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// Presburger-fs is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with Foobar.  If not, see <https://www.gnu.org/licenses/>.
//
// Copyright 2018 cannorin

module PresburgerFs.Solve
open PresburgerFs.Expr
open PresburgerFs.Formula
open FSharpPlus

let rec eliminateForall (fml: OriginFormula) : OriginFormulaWithoutForall =
  match fml with
    | FmlAtomic a -> FmlAtomic a
    | FmlConjunction (l, r) -> FmlConjunction (eliminateForall l, eliminateForall r)
    | FmlDisjunction (l, r) -> FmlDisjunction (eliminateForall l, eliminateForall r)
    | FmlNegate f -> FmlNegate (eliminateForall f)
    | FmlQuantifier (QFEExists, var, scope) ->
      FmlQuantifier (QENExists, var, eliminateForall scope)
    | FmlQuantifier (QFEForall, var, scope) ->
      FmlQuantifier (QENNotExists, var, FmlNegate (eliminateForall scope))

let rec toPrenexForm (fml: OriginFormulaWithoutForall) : PrenexFormula =
  let inline treatBinOp cstr l r =
    match toPrenexForm l, toPrenexForm r with
      | PFMatrix l', PFMatrix r' ->
        PFMatrix (cstr (l', r'))
      | PFMatrix m, PFQuantifier (q, var, scope)
      | PFQuantifier (q, var, scope), PFMatrix m ->
        let scope' = scope >>= fun x -> cstr (m, x) |> PFMatrix
        PFQuantifier (q, var, scope')
      | PFQuantifier (lq, lv, ls), PFQuantifier (rq, rv, rs) ->
        let scope' =
          ls >>= fun l ->
            rs >>= fun r ->
              cstr (l, r) |> PFMatrix
        PFQuantifier (lq, lv, PFQuantifier (rq, rv, scope'))        
  match fml with
    | FmlAtomic a -> PFMatrix (PAtomic a)
    | FmlConjunction (l, r) -> treatBinOp PConjunction l r
    | FmlDisjunction (l, r) -> treatBinOp PDisjunction l r
    | FmlNegate x ->
      match toPrenexForm x with
        | PFQuantifier (QENExists, v, s)    -> PFQuantifier (QENNotExists, v, s)
        | PFQuantifier (QENNotExists, v, s) -> PFQuantifier (QENExists, v, s)
        | PFMatrix m -> PFMatrix (PNegate m)
    | FmlQuantifier (q, var, scope) ->
      PFQuantifier (q, var, toPrenexForm scope)

let toNegationNormalForm (fml: PrenexFormula) : PrenexNNFFormula =
  let rec f = function
    | PAtomic a -> NNFAtomic a
    | PConjunction (l, r) -> NNFConjunction (f l, f r)
    | PDisjunction (l, r) -> NNFDisjunction (f l, f r)
    | PNegate (PAtomic a) -> NNFNegate a
    | PNegate (PNegate x) -> f x
    | PNegate (PConjunction (l, r)) ->
      NNFDisjunction (l |> PNegate |> f, r |> PNegate |> f)
    | PNegate (PDisjunction (l, r)) ->
      NNFConjunction (l |> PNegate |> f, r |> PNegate |> f)
  fml |> map f

let eliminateCompareOps (fml: PrenexNNFFormula) : PrenexNNFLtFormula =
  let inline complt t u = AFComparison (ComparisonLt, t, u) |> NNFAtomic
  let inline compeq t u = AFComparison (CompEq, t, u) |> NNFAtomic
  let rec f = function
    | NNFConjunction (l, r) -> NNFConjunction (f l, f r)
    | NNFDisjunction (l, r) -> NNFDisjunction (f l, f r)
    | NNFDisjunctSumForRange (v, u, x) -> NNFDisjunctSumForRange (v, u, f x)
    | NNFDisjunctSumInSet    (v, s, x) -> NNFDisjunctSumInSet    (v, s, f x)
    | NNFAtomic a ->
     match a with
        | AFTrue  -> NNFAtomic AFTrue
        | AFFalse -> NNFAtomic AFFalse
        | AFDivisiblity dc -> AFDivisiblity dc |> NNFAtomic
        | AFComparison (CompLt, s, t) -> complt s t
        | AFComparison (CompGt, s, t) -> complt t s
        | AFComparison (CompEq, s, t) ->
          NNFConjunction (complt s (t + ENum 1), complt t (s + ENum 1))
        | AFComparison (CompLte, s, t) ->
          NNFDisjunction (complt s t, compeq s t |> f)
        | AFComparison (CompGte, s, t) ->
          NNFDisjunction (complt t s, compeq s t |> f)
    | NNFNegate a ->
      match a with
        | AFTrue  -> NNFAtomic AFFalse
        | AFFalse -> NNFAtomic AFTrue
        | AFDivisiblity dc -> NNFNegate dc
        | AFComparison (CompLt, s, t) -> complt t (s + ENum 1)
        | AFComparison (CompGt, s, t) -> complt s (t + ENum 1)
        | AFComparison (CompEq, s, t) ->
          NNFDisjunction (complt s t, complt t s)
        | AFComparison (CompLte, s, t) -> complt t s
        | AFComparison (CompGte, s, t) -> complt s t
  fml |> map f

let removeDuplicatesInAtomic (fml: PrenexNNFLtFormula) : PrenexNNFLtFormula =
  let rdOver (var: string) (qff: QuantifierFreeFormula) : QuantifierFreeFormula =
    qff |> bimap id (
      fun (ComparisonLt, lhs, rhs) ->
        match Expr.count var lhs, Expr.count var rhs with
          | (0, _) | (_, 0) -> (ComparisonLt, lhs, rhs)
          | (ln, rn) ->
            let diff = max ln rn - min ln rn
            if ln > rn then 
              (ComparisonLt, lhs - EVar var * diff, rhs |> Expr.subst var (ENum zero))
            else
              (ComparisonLt, lhs |> Expr.subst var (ENum zero), rhs - EVar var * diff)
    )
  let qvs = fml |> toSeq |> Seq.map snd
  fml |> map (fun x ->
    qvs |> Seq.fold (flip rdOver) x
  )

let lcmAllCoefficientsToBoundVariables (fml: PrenexNNFLtFormula) : PrenexNNFLtFormula =
  undefined ()

let eliminateQuantifiers (fml: PrenexNNFLtFormula) : QuantifierFreeFormula =
  undefined ()

