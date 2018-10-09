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

let rec eliminateForall (fml: Formula<_>) : FormulaWithoutForall<_> =
  match fml with
    | G0 a -> G0 a
    | Gn (c, xs) -> Gn (c, xs |> Seq.map eliminateForall)
    | G1 (FNegate, n) -> G1 (FNegate, eliminateForall n)
    | G1 (FQuantifier (QFEExists v), n) -> G1 (FQuantifier (QENExists v), eliminateForall n)
    | G1 (FQuantifier (QFEForall v), n) -> G1 (FQuantifier (QENNotExists v), G1 (FNegate, eliminateForall n))

let rec toPrenexForm (fml: FormulaWithoutForall<_>) : PrenexFormula<_> =
  let treatBinop (cstr: PrenexMatrix<_> seq -> PrenexMatrix<_>)
                 (xs: FormulaWithoutForall<_> seq)
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
      match toPrenexForm x with
        | PFQuantifier (QENExists v, s)    -> PFQuantifier (QENNotExists v, s)
        | PFQuantifier (QENNotExists v, s) -> PFQuantifier (QENExists v, s)
        | PFMatrix m -> PFMatrix (G1 (Negate, m))
    | G1 (FQuantifier q, scope) ->
      PFQuantifier (q, toPrenexForm scope)

let toNegationNormalForm (fml: PrenexFormula<_>) : PrenexNNFFormula<_> =
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
    | G1 ((), _) -> failwith "impossible"
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
          | (0, _) | (_, 0) -> ac (ComparisonLt, lhs, rhs)
          | (ln, rn) ->
            let diff = max ln rn - min ln rn
            if ln > rn then 
              ac (ComparisonLt, lhs - Expression.multiply diff (Expression.variable var), rhs |> Expression.subst var (Expression.constant 0))
            else
              ac (ComparisonLt, lhs |> Expression.subst var (Expression.constant zero), rhs - Expression.multiply diff (Expression.variable var))
      | x -> x
    )
  let qvs = fml |> toSeq |> Seq.map varOfQuantifier
  fml |> map (fun x ->
    qvs |> Seq.fold (flip rdOver) x
  )

let inline lcm (x: ^n) (y: ^n) =
  abs (x * y) / FSharpPlus.Math.Generic.gcd x y

let inline normalizeAllCoefficientsToOne (fml: PrenexNNFLtFormula<_>) : PrenexNNFLtFormula<_> =
  let inline nmOver (var: string) (mtx: PrenexNNFLtMatrix<_>) : PrenexNNFLtMatrix<_> =
    let lcm = 
      mtx |> toSeq
          |> Seq.collect toSeq
          |> Seq.map (Expression.count var)
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
                
                let ml = lcm / (Expression.count var lhs + Expression.count var rhs)
                if Expression.count var lhs > 0 || Expression.count var rhs < 0 then
                  AFComparison (ComparisonLt, Expression.multiply ml lhs |> cfOne, Expression.multiply ml rhs |> cfZero)
                else
                  AFComparison (ComparisonLt, Expression.multiply ml lhs |> cfZero, Expression.multiply ml rhs |> cfOne)
              | AFDivisiblity dc ->
                let ml = lcm / (dc.dividend |> Expression.count var)
                dc |> bimap ((*) (uint32 ml)) (Expression.multiply ml >> cfOne) |> AFDivisiblity
        | NNFNegate dc ->
          let ml = lcm / (dc.dividend |> Expression.count var)
          dc |> bimap ((*) (uint32 ml)) (Expression.multiply ml >> cfOne) |> NNFNegate
        )
    
    Conjunction (
      G0 (NNFAtomic (AFDivisiblity { dividend = Expression.variable var; divisor = uint32 lcm })),
      qff'
    )
  let qvs = fml |> toSeq |> Seq.map varOfQuantifier
  fml |> map (fun x ->
    qvs |> Seq.fold (flip nmOver) x
  )

let inline eliminateQuantifiers (fml: PrenexNNFLtFormula<_>) : EliminatedFormula<_> =
  let inline eliminateOver (var: string) (mtx: PrenexNNFLtMatrix<_>) : EliminatedFormula<_> =
    let delta =
      mtx |> toSeq
          |> Seq.choose (function
              | NNFAtomic (AFDivisiblity dc)
              | NNFNegate dc -> Some dc
              | _ -> None
             )
          |> Seq.filter (fun dc -> dc.dividend |> Expression.contains var)
          |> Seq.map (fun dc -> int dc.divisor)
          |> Seq.fold lcm 1
    
    let f51 : PrenexNNFLtMatrix<_> =
      let qffNegInf =
        mtx |> map
          (function
            | NNFAtomic (AFComparison (_, lhs, _)) when lhs |> Expression.contains var -> AFTrue  |> NNFAtomic
            | NNFAtomic (AFComparison (_, _, rhs)) when rhs |> Expression.contains var -> AFFalse |> NNFAtomic
            | x -> x
          )
      DisjunctSumForRange (var, delta, qffNegInf)
    
    let solutionCanBeInfinitelySmall =
      let rec check = function
        | G0 (NNFAtomic (AFComparison (_, lhs, rhs)))
          when lhs |> Expression.isConstant |> Option.isSome && rhs |> Expression.contains var -> false
        | G0 _ -> true
        | Gn (LConjunction, xs) -> xs |> Seq.exists check
        | Gn (LDisjunction, xs) -> xs |> Seq.forall check
        | G1 _ -> failwith "impossible"
      check mtx
    
    if solutionCanBeInfinitelySmall then G0 f51
    else
      let b =
        mtx |> toSeq
            |> Seq.choose (function
                | NNFAtomic (AFComparison (_, lhs, rhs))
                  when rhs |> Expression.contains var ->
                    let rhs' = rhs |> Expression.remove var
                    Some (lhs - rhs')
                | _ -> None
               )
      let newName =
        let exprs =
          mtx |> toSeq
              |> Seq.collect toSeq
              |> Seq.toArray
        var |> Seq.unfold (fun v -> let v' = sprintf "%s'" v in Some (v',v'))
            |> Seq.find (fun v -> exprs |> Seq.forall (Expression.contains v >> not))
      let f52 : PrenexNNFLtMatrix<_> =
        DisjunctSumForRange (var, delta,
          DisjunctSumInSet (newName, b |> Seq.toList,
            mtx |> map (map (Expression.subst var (Expression.variable var + Expression.variable newName)))
          )
        )
      Disjunction (G0 f51, G0 f52)
  let rec eliminate : PrenexNNFLtFormula<_> -> EliminatedFormula<_> = function
    | PFQuantifier (QENNotExists v, x) ->
      G1 (Negate, eliminate (PFQuantifier (QENExists v, x)))
    | PFQuantifier (QENExists v, PFMatrix qff) ->
      eliminateOver v qff
    | PFQuantifier (QENExists v, x) ->
      eliminate x >>= (eliminateOver v)
    | PFMatrix _ -> failwith "impossible"
  eliminate fml

let inline eliminate fml =
  fml |> eliminateForall
      |> toPrenexForm
      |> toNegationNormalForm
      |> eliminateCompareOps
      |> removeDuplicatesInAtomic
      |> normalizeAllCoefficientsToOne
      |> eliminateQuantifiers