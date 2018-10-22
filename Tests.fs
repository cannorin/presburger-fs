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

module PresburgerFs.Tests

#if DEBUG
open PresburgerFs.Expr
open PresburgerFs.Formula
open PresburgerFs.Elimination
open FsCheck

module TestObjects =
  [<StructuredFormatDisplay("{str}")>]
  type TestFormula =
    | TFTrue | TFFalse
    | TFComparison of ComparisonOps * Expr * Expr
    | TFConjunction of TestFormula * TestFormula
    | TFDisjunction of TestFormula * TestFormula
    | TFNegate of TestFormula
    | TFForall of string * TestFormula
    | TFExists of string * TestFormula
    with
      override this.ToString() = sprintf "%A" this
      static member FV x =
        match x with
          | TFComparison (_, l, r) -> Seq.append (fvOf l) (fvOf r)
          | TFConjunction (l, r)
          | TFDisjunction (l, r) -> Seq.append (fvOf l) (fvOf r)
          | TFNegate x -> fvOf x
          | TFForall (v, x)
          | TFExists (v, x) -> fvOf x |> Seq.filter ((<>) v)
          | TFTrue | TFFalse -> Seq.empty

  let rec toGenericFormula (x: TestFormula) : Formula<Expr> =
    match x with
      | TFTrue -> G0 (AFTrue) | TFFalse -> G0 (AFFalse)
      | TFComparison (c, l, r) -> G0 (AFComparison (c, l, r))
      | TFConjunction (l, r) -> Conjunction (toGenericFormula l, toGenericFormula r)
      | TFDisjunction (l, r) -> Disjunction (toGenericFormula l, toGenericFormula r)
      | TFNegate x -> G1 (FNegate, toGenericFormula x)
      | TFForall (v, x) -> G1 (FQuantifier (QFEForall v), toGenericFormula x)
      | TFExists (v, x) -> G1 (FQuantifier (QFEExists v), toGenericFormula x)

  type TestFormula with
    member this.str = sprintf "%A" (toGenericFormula this)

  [<StructuredFormatDisplay("{str}")>]
  type ClosedTestFormula = ClosedTestFormula of TestFormula with
    member this.str = let (ClosedTestFormula c) = this in sprintf "%A" c
    override this.ToString() = this.str

  type StringName =
    static member Name() =
      Arb.Default.String()
      |> Arb.filter (fun x -> 
         String.length x > 0
         && x |> String.forall System.Char.IsLetter
         && x |> String.forall System.Char.IsLower
         )

  let genExprFromVars (varlist: string list) =
    gen {
      let! num = Arb.generate<int>
      let! vars =
        Gen.nonEmptyListOf <|
          gen {
            let! v =
              if List.isEmpty varlist then
                Gen.constant (ENum 0)
              else Gen.elements varlist |> Gen.map EVar
            let! m = Arb.generate<int>
            return m * v
          }
      return ENum num + Seq.sum vars
    }

  let genFormulaFromVars varlist =
    let inline divideBy n x = x / n
    let rec fmlgen size varlist =
      gen {
        let cmpl =
          Gen.map3 (fun c l r -> TFComparison (c, l, r))
                   Arb.generate<ComparisonOps>
                   (genExprFromVars varlist)
                   (genExprFromVars varlist)
        let op2 cstr =
          Gen.map2 (fun l r -> cstr (l, r))
                   (fmlgen (divideBy 2 size) varlist)
                   (fmlgen (divideBy 2 size) varlist)
        let neg =
          fmlgen (divideBy 2 size) varlist |> Gen.map TFNegate
        let qf cstr =
          gen {
            let! name = Arb.generate<string>
            let name =
              let vars =
                Seq.unfold (fun state -> let a = sprintf "%s'" state in Some (state, a)) name
              vars |> Seq.find (fun x -> varlist |> List.contains x |> not)
                
            let! body = fmlgen (divideBy 3 size) (name :: varlist)
            return cstr (name, body)
          }
        
        if size > 2 then
          return! Gen.frequency [ 
            3, cmpl;
            1, op2 TFConjunction;
            1, op2 TFDisjunction;
            1, neg;
            2, qf TFForall;
            2, qf TFExists
          ]
        else
          return! cmpl
      }
    Gen.sized (fun i -> fmlgen i varlist)

  type Generators =
    static member Formula =
      gen {
        let! vars = Gen.nonEmptyListOf Arb.generate<string>
        return! genFormulaFromVars vars
      } |> Arb.fromGen
    static member ClosedFormula =
      genFormulaFromVars [] |> Gen.map ClosedTestFormula |> Arb.fromGen

open TestObjects

type TautologicalProperties =
  static member `` Comparison works correctly ``
    (co: ComparisonOps) (a: int) (b: int) =
    let expected =
      match co with
        | CompEq -> a = b | CompLt -> a < b | CompGt -> a > b
        | CompLte -> a <= b | CompGte -> a >= b
    let result =
      TFComparison (co, ENum a, ENum b) |> toGenericFormula |> eliminate
    result = truthValue expected
  
  static member `` Negation of comparison works correctly ``
    (co: ComparisonOps) (a: int) (b: int) =
    let expected =
      match co with
        | CompEq -> a = b | CompLt -> a < b | CompGt -> a > b
        | CompLte -> a <= b | CompGte -> a >= b
    let result =
      TFNegate (TFComparison (co, ENum a, ENum b)) |> toGenericFormula |> eliminate
    result = truthValue (not expected)

type ClosedFormulaProperties =
  static member `` Every closed formula is either valid or unsatisfiable ``
    (ClosedTestFormula fml) =
    let fml' = fml |> toGenericFormula |> eliminate
    fml' = truthValue true || fml' = truthValue false
  
  static member `` Every closed formula and its negation cannot have the same truth value ``
    (ClosedTestFormula fml) =
    let nfml = TFNegate fml
    let e x = x |> toGenericFormula |> eliminate
    e fml <> e nfml

type FormulaProperties =
  static member `` Free variables should not increase after elimination ``
    (fml: TestFormula) =
    let fml = toGenericFormula fml
    let fvBefore = fvOf fml |> Set.ofSeq
    let fvAfter  = eliminate fml |> fvOf |> Set.ofSeq
    Set.isSubset fvAfter fvBefore

let run () =
  Arb.register<StringName>() |> ignore
  Arb.register<Generators>() |> ignore

  let config = { Config.Quick with MaxTest = 100; EndSize=40 }
  Check.All<TautologicalProperties> config
  Check.All<ClosedFormulaProperties> config
  Check.All<FormulaProperties> config

#endif