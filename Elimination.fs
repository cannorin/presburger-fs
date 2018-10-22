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
// along with Presburger-fs.  If not, see <https://www.gnu.org/licenses/>.
//
// Copyright 2018 cannorin

module PresburgerFs.Elimination
open PresburgerFs.Expr
open PresburgerFs.Formula
open FSharpPlus

let rec toPrenexForm (fml: Formula<_>) : PrenexFormula<_> =
  let treatBinop (cstr: PrenexMatrix<_> seq -> PrenexMatrix<_>)
                 (xs: Formula<_> seq)
                 : PrenexFormula<_> =
    assert (Seq.isEmpty xs |> not)
    let h, t = Seq.head xs, Seq.tail xs
    t |> Seq.fold (fun state x ->
           state >>= fun xs ->
             toPrenexForm x >>= fun x ->
               seq { yield x; yield! xs } |> PFMatrix
         ) (h |> toPrenexForm |> map Seq.singleton)
      |> map cstr
  match fml with
    | G0 a -> PFMatrix (G0 a)
    | Gn (n, xs) -> treatBinop (fun xs -> Gn (n, xs)) xs
    | G1 (FNegate, x) ->
      match x with
        | G1 (FQuantifier (QFEForall v), scope) ->
          PFQuantifier (QFEExists v, G1 (FNegate, scope) |> toPrenexForm)
        | G1 (FQuantifier (QFEExists v), scope) ->
          PFQuantifier (QFEForall v, G1 (FNegate, scope) |> toPrenexForm)
        | G1 (FNegate, x) -> toPrenexForm x
        | Gn (LConjunction, xs) ->
          Gn (LDisjunction, xs |> Seq.map (fun x -> G1 (FNegate, x))) |> toPrenexForm
        | Gn (LDisjunction, xs) ->
          Gn (LConjunction, xs |> Seq.map (fun x -> G1 (FNegate, x))) |> toPrenexForm
        | G0 x -> PFMatrix (G1 (Negate, G0 x))
    | G1 (FQuantifier q, scope) ->
      PFQuantifier (q, toPrenexForm scope)

let rec eliminateForall (fml:PrenexFormula<_>) : PrenexFormulaWithoutForall<_> =
  match fml with
    | PFQuantifier (QFEExists v, x) -> PFQuantifier (QENExists v, eliminateForall x)
    | PFQuantifier (QFEForall v, x) ->
      PFQuantifier (QENNotExists v, 
        match eliminateForall x with
          | PFMatrix x -> G1 (Negate, x) |> PFMatrix
          | PFQuantifier (QENExists v, x)    -> PFQuantifier (QENNotExists v, x)
          | PFQuantifier (QENNotExists v, x) -> PFQuantifier (QENExists v, x)
      )
    | PFMatrix x -> PFMatrix x

let toNegationNormalForm (fml: PrenexFormulaWithoutForall<_>) : PrenexNNFFormula<_> =
  let rec f = function
    | G0 a -> G0 (NNFAtomic a)
    | Gn (n, xs) -> Gn (n, xs |> Seq.map f)
    | G1 (Negate, G0 a) -> G0 (NNFNegate a)
    | G1 (Negate, G1 (Negate, x)) -> f x
    | G1 (Negate, Gn (LConjunction, xs)) ->
      Gn (LDisjunction, xs |> Seq.map (fun x -> G1 (Negate, x) |> f))
    | G1 (Negate, Gn (LDisjunction, xs)) ->
      Gn (LConjunction, xs |> Seq.map (fun x -> G1 (Negate, x) |> f))
  fml |> map f

let inline eliminateCompareOps (fml: PrenexNNFFormula<_>) : PrenexNNFLtFormula<_> =
  let inline complt t u = AFComparison (ComparisonLt, t, u) |> NNFAtomic |> G0
  let inline compeq t u = AFComparison (CompEq, t, u) |> NNFAtomic |> G0
  let rec f = function
    | Gn (n, xs) -> Gn (n, xs |> Seq.map f)
    | G1 (Empty, _) -> failwith "impossible"
    | G0 (NNFAtomic a) ->
     match a with
        | AFTrue  -> NNFAtomic AFTrue |> G0
        | AFFalse -> NNFAtomic AFFalse |> G0
        | AFDivisiblity dc -> AFDivisiblity dc |> NNFAtomic |> G0
        | AFComparison (CompLt, s, t) -> complt s t
        | AFComparison (CompGt, s, t) -> complt t s
        | AFComparison (CompEq, s, t) ->
          Conjunction (complt s (t + Expression.constant one), complt t (s + Expression.constant one))
        | AFComparison (CompLte, s, t) ->
          Disjunction (complt s t, compeq s t |> f)
        | AFComparison (CompGte, s, t) ->
          Disjunction (complt t s, compeq s t |> f)
    | G0 (NNFNegate a) ->
      match a with
        | AFTrue  -> NNFAtomic AFFalse |> G0
        | AFFalse -> NNFAtomic AFTrue |> G0
        | AFDivisiblity dc -> NNFNegate dc |> G0
        | AFComparison (CompLt, s, t) -> complt t (s + Expression.constant one)
        | AFComparison (CompGt, s, t) -> complt s (t + Expression.constant one)
        | AFComparison (CompEq, s, t) ->
          Disjunction (complt s t, complt t s)
        | AFComparison (CompLte, s, t) -> complt t s
        | AFComparison (CompGte, s, t) -> complt s t
  fml |> map f

let inline removeDuplicatesInAtomic (fml: PrenexNNFLtFormula<_>) : PrenexNNFLtFormula<_> =
  let inline rdOver (var: string) (mtx: PrenexNNFLtMatrix<_>) : PrenexNNFLtMatrix<_> =
    mtx |> map (function
      | NNFAtomic (AFComparison (ComparisonLt, lhs, rhs)) ->
        let inline ac x = NNFAtomic (AFComparison x)
        match Expression.count var lhs, Expression.count var rhs with
          | (0, n) | (n, 0) when n <> 0 -> ac (ComparisonLt, lhs, rhs)
          | (ln, rn) ->
            let diff = max ln rn - min ln rn
            if diff = 0 then
              ac (ComparisonLt, lhs |> Expression.remove var, rhs |> Expression.remove var)
            else
              if ln > rn then 
                ac (ComparisonLt, lhs - Expression.multiply diff (Expression.variable var), rhs |> Expression.remove var)
              else
                ac (ComparisonLt, lhs |> Expression.remove var, rhs - Expression.multiply diff (Expression.variable var))
      | x -> x
    )
  let qvs = fml |> toSeq |> Seq.map varOfQuantifier
  fml |>> fun x ->
    qvs |> Seq.fold (flip rdOver) x

let inline private lcm (x: ^n) (y: ^n) =
  abs (x * y) / FSharpPlus.Math.Generic.gcd x y

let inline normalizeAllCoefficientsToOne (fml: PrenexNNFLtFormula<_>) : PrenexNNFLtFormula<_> =
  let inline nmOver (var: string) (mtx: PrenexNNFLtMatrix<_>) : PrenexNNFLtMatrix<_> =
    let lcm = 
      mtx |> toSeq
          |> Seq.collect toSeq
          |> Seq.map (Expression.count var)
          |> Seq.filter ((<>) 0)
          |> Seq.fold lcm one

    let inline cfOne expr =
      Expression.variable var + (expr |> Expression.remove var)
    let inline cfZero expr = expr |> Expression.remove var
    
    let qff' = 
      mtx |> map (function
        | NNFAtomic a ->  
          NNFAtomic <|
            match a with
              | AFFalse -> AFFalse | AFTrue -> AFTrue
              | AFComparison (ComparisonLt, lhs, rhs) ->
                // During this manipulation, atomic formulas must only contain
                // 1 occurrence of the variable at most.
                assert (not (Expression.contains var lhs) || not (Expression.contains var rhs)) 

                let count = Expression.count var lhs + Expression.count var rhs
                if count = 0 then a
                else
                  let ml = lcm / count
                  if Expression.count var lhs > 0 || Expression.count var rhs < 0 then
                    AFComparison (ComparisonLt, Expression.multiply ml lhs |> cfOne, Expression.multiply ml rhs |> cfZero)
                  else
                    AFComparison (ComparisonLt, Expression.multiply ml lhs |> cfZero, Expression.multiply ml rhs |> cfOne)
              | AFDivisiblity dc ->
                let count = dc.dividend |> Expression.count var
                if count = 0 then a
                else
                  let ml = lcm / count
                  dc |> bimap ((*) (uint32 ml)) (Expression.multiply ml >> cfOne) |> AFDivisiblity
        | NNFNegate dc ->
          let count = dc.dividend |> Expression.count var
          if count = 0 then NNFNegate dc
          else
            let ml = lcm / count
            dc |> bimap ((*) (uint32 ml)) (Expression.multiply ml >> cfOne) |> NNFNegate
        )
    
    Conjunction (
      G0 (NNFAtomic (AFDivisiblity { dividend = Expression.variable var; divisor = uint32 lcm })),
      qff'
    )
  let qvs = fml |> toSeq |> Seq.map varOfQuantifier
  fml |>> fun x ->
    qvs |> Seq.fold (flip nmOver) x

let inline eliminateQuantifiers (fml: PrenexNNFLtFormula<_>) : EliminatedFormula<_> =
  let inline eliminateOver (var: string) (mtx: PrenexNNFLtMatrix<_>) : EliminatedFormula<_> =
    let atomics = mtx |> toSeq |> Seq.distinct |> Seq.cache

    startClock ()
    let delta =
      atomics |> Seq.fold (fun state -> 
               function
                 | NNFAtomic (AFDivisiblity dc)
                 | NNFNegate dc when Expression.contains var dc.dividend ->
                   lcm state (int dc.divisor)
                 | _ -> state
             ) 1
    check "delta" ()
    
    let f51 : PrenexNNFLtMatrix<_> =
      let qffNegInf =
        mtx |> map
          (function
            | NNFAtomic (AFComparison (_, lhs, _))
              when lhs |> Expression.contains var -> AFTrue  |> NNFAtomic
            | NNFAtomic (AFComparison (_, _, rhs))
              when rhs |> Expression.contains var -> AFFalse |> NNFAtomic
            | x -> x
          )
      DisjunctSumForRange (var, delta, qffNegInf)
    check "f51" ()
    
    let solutionCanBeInfinitelySmall =
      let rec check = function
        | G0 (NNFAtomic (AFComparison (_, _, rhs)))
          when rhs |> Expression.contains var -> false
        | G0 _ -> true
        | Gn (LConjunction, xs) -> xs |> Seq.forall check
        | Gn (LDisjunction, xs) -> xs |> Seq.exists check
        | G1 _ -> failwith "impossible"
      check mtx
    check "solutionCanBeInfinitelySmall" ()
    
    if solutionCanBeInfinitelySmall then
      G0 f51 |> reduce |> check "reduce(f51)"
    else
      let b =
        atomics
          |> Seq.choose (function
              | NNFAtomic (AFComparison (_, lhs, rhs))
                when rhs |> Expression.contains var ->
                  let rhs' = rhs |> Expression.remove var
                  Some (lhs - rhs')
              | _ -> None
             )
          |> Seq.distinct
          |> Seq.cache
      check "b" ()

      let newName =
        let exprs =
          atomics |> Seq.collect (toSeq >> Seq.collect fvOf)
                  |> Seq.cache
        var |> Seq.unfold (fun v -> let v' = sprintf "%s'" v in Some (v',v'))
            |> Seq.find (fun v -> exprs |> Seq.contains v |> not)
      check "newName" ()

      let f52 : PrenexNNFLtMatrix<_> =
        DisjunctSumForRange (var, delta,
          DisjunctSumInSet (newName, b,
            mtx |>> map (Expression.subst var (Expression.variable var + Expression.variable newName))
          )
        )
      check "f52" ()

      Disjunction (G0 f51, G0 f52) |> reduce |> check "reduce(f51 v f52)"

  let rec eliminate : PrenexNNFLtFormula<_> -> EliminatedFormula<_> = function
    | PFQuantifier (QENNotExists v, x) ->
      G1 (Negate, eliminate (PFQuantifier (QENExists v, x)))
    | PFQuantifier (QENExists v, PFMatrix qff) ->
      eliminateOver v qff
    | PFQuantifier (QENExists v, x) ->
      eliminate x >>= (eliminateOver v)
    | PFMatrix x ->
      G0 x
  eliminate fml

let inline eliminate (fml: Formula< ^a >) : EliminatedFormula< ^a > =
  startClock ()
  let res =
    fml |> toPrenexForm
        |> check "toPrenexForm"
        |> eliminateForall
        |> check "eliminateForall"
        |> toNegationNormalForm
        |> check "toNegationNormalForm"
        |> eliminateCompareOps
        |> check "eliminateCompareOps"
        |> map reduce
        |> check "map reduce"
        |> removeDuplicatesInAtomic
        |> check "removeDuplicatesInAtomic"
        |> normalizeAllCoefficientsToOne
        |> check "normalizeAllCoefficientsToOne"
        |> eliminateQuantifiers
        |> check "eliminateQuantifiers"
        |> reduce
  
  #if DEBUG
  sw.Stop()
  #endif
  res