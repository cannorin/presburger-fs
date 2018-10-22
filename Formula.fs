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

module PresburgerFs.Formula
open PresburgerFs.Expr
open FSharpPlus
open FSharp.Collections

let inline isTautology (fml: ^X) =
  (^X: (static member IsTautology: ^X -> bool option) fml)

let inline compareBy (cmp: ^Cmp) x y =
  (^Cmp: (static member CompareBy: ^Cmp * _ * _ -> bool option) cmp,x,y)

let inline truthValue b : ^F = (^F: (static member TruthValue: bool -> ^F) b)

let inline reduce (fml: ^Fml) : ^Fml = (^Fml: (static member Reduce: ^Fml -> ^Fml) fml)

let inline reduceBy (op: ^Op) (cstr: ^Arg -> ^Fml) (arg: ^Arg) : ^Fml =
  (^Op: (static member ReduceBy: ^Op * (^Arg -> ^Fml) * ^Arg -> ^Fml) op, cstr, arg)

let inline fvOf (fml: ^Fml) =
  (^Fml: (static member FV: ^Fml -> seq<string>) fml)

let inline filterFv (o: ^Op) (fv: seq<string>) =
  (^Op: (static member FilterFV: ^Op * seq<string> -> seq<string>) o,fv)

///     Bifunctor<nat, 'Term>, Foldable<'Term>, Tautology, Reducible
[<Struct; StructuredFormatDisplay("{str}")>]
type DivisibilityConstant<'Term> = {
  divisor:  nat
  dividend: 'Term
} with
  member this.str =
    sprintf "%i|%A" this.divisor this.dividend
  static member inline FV x = fvOf x.dividend
  static member inline Bimap (x, f, g) =
    { divisor = f x.divisor; dividend = g x.dividend }
  static member inline ToSeq x = seq [x.dividend]
  static member inline IsTautology x =
    if x.divisor = 1u then Some true
    else
      Expression.isConstant x.dividend 
      |> Option.map (fun n -> n % int x.divisor = 0)
  static member inline Reduce x = x

///     Functor<'Term>, Foldable<'Term>, Tautology, TruthValue
and [<Struct; StructuredFormatDisplay("{str}")>] 
AtomicFormula<'Comparison, 'Term> =
  | AFComparison   of cmp:'Comparison * lhs:'Term * rhs:'Term
  | AFDivisiblity  of DivisibilityConstant<'Term>
  | AFTrue | AFFalse
  with
    member this.str =
      match this with
        | AFTrue -> "T" | AFFalse -> "F"
        | AFDivisiblity d -> sprintf "%A" d
        | AFComparison (c, l, r) -> sprintf "%A %A %A" l c r
    static member inline FV x =
      match x with
        | AFDivisiblity dc -> fvOf dc
        | AFComparison (_, l, r) -> Seq.append (fvOf l) (fvOf r)
        | _ -> Seq.empty
    static member Map (x, f) =
      match x with
        | AFComparison (c, l, r) -> AFComparison (c, f l, f r)
        | AFDivisiblity dc -> AFDivisiblity (map f dc)
        | AFTrue -> AFTrue | AFFalse -> AFFalse
    static member ToSeq x =
      match x with
        | AFComparison (_, l, r) -> seq [l;r]
        | AFDivisiblity dc -> toSeq dc
        | _ -> Seq.empty
    static member inline IsTautology x =
      match x with
        | AFTrue -> Some true | AFFalse -> Some false
        | AFDivisiblity dc -> isTautology dc
        | AFComparison (c, l, r) -> compareBy c l r
    static member inline TruthValue b =
      if b then AFTrue else AFFalse
    static member inline Reduce x = x

///     Monad<'G0>, Foldable<'G0>, Tautology, TruthValue, Reducible
[<StructuredFormatDisplay("{str}")>]
type GenericFormula< 'G0, 'G1, 'Gn > =
  | G0 of 'G0
  | G1 of 'G1 * GenericFormula<'G0, 'G1, 'Gn>
  | Gn of 'Gn * GenericFormula<'G0, 'G1, 'Gn> seq
  with
    member inline this.str =
      match this with
        | G0 x -> sprintf "%A"x 
        | G1 (o, x) -> sprintf "%A %A" o x
        | Gn (n, xs) -> 
          xs |> Seq.map (sprintf "%A") |> String.concat (sprintf "%A" n) |> sprintf "(%s)"
    static member inline FV x =
      let rec fv = function
        | G0 x -> fvOf x
        | G1 (o, x) -> fv x |> filterFv o
        | Gn (n, xs) -> xs |> Seq.collect fv |> filterFv n
      fv x
    static member inline (>>=) (x, f) =
      let rec bind = function
        | G0 x -> f x
        | G1 (o, x) -> G1 (o, bind x)
        | Gn (n, xs) -> Gn (n, xs |> Seq.map bind)
      bind x
    static member inline Return x = G0 x 
    static member inline ToSeq x =
      let rec ts = function
        | G0 x -> Seq.singleton x
        | G1 (_, x) -> ts x
        | Gn (_, xs) -> xs |> Seq.collect ts
      ts x
    static member inline TruthValue b = G0 (truthValue b)
    static member inline Reduce fml =
      let rec r = function
        | G0 x -> let x = reduce x in isTautology x |> Option.map truthValue ?| G0 x
        | G1 (o, x)  -> r x |> reduceBy o (fun x -> G1 (o, x))
        | Gn (n, xs) -> xs |> Seq.map r |> reduceBy n (fun xs -> Gn (n, xs))
      r fml
    static member inline IsTautology fml =
      if fml = G0 (truthValue true) then Some true
      else if fml = G0 (truthValue false) then Some false
      else None

///     ReducibleBy
[<Struct; StructuredFormatDisplay("{str}")>]
type LogicalOp = LConjunction | LDisjunction
  with
    member this.str = match this with LConjunction -> " ^ " | LDisjunction -> " v "
    static member inline FilterFV (_: LogicalOp, xs) = xs
    static member inline ReduceBy (op, cstr: ^Fml seq -> ^Fml, xs: ^Fml seq) : ^Fml =
      startClock ()
      let xs =
        xs |> Seq.map (fun x ->
                if x = truthValue true then Choice1Of2 true
                else if x = truthValue false then Choice1Of2 false
                else Choice2Of2 x
              )
           |> Seq.cache
      let inline isTruth (b: bool) x = match x with Choice1Of2 b' -> b = b' | _ -> false
      let inline rem x = match x with Choice2Of2 x -> Some x | Choice1Of2 _ -> None
      match op with
        | LConjunction ->
          if xs |> Seq.exists (isTruth false) |> check "CONJ exists false" then truthValue false
          else
            let xs = xs |> Seq.choose rem |> Seq.cache |> check "choose rem"
            if Seq.isEmpty xs then truthValue true
            else if Seq.length xs = 1 then Seq.head xs
            else cstr xs
        | LDisjunction ->
          if xs |> Seq.exists (isTruth true) |> check "DISJ exists true " then truthValue true
          else
            let xs' = xs |> Seq.choose rem |> Seq.cache |> check "choose rem"
            if Seq.isEmpty xs' then xs |> Seq.exists (isTruth false) |> not |> truthValue |> check "DISJ exists false"
            else if Seq.length xs' = 1 then Seq.head xs'
            else cstr xs'

let inline Conjunction (l, r) = Gn (LConjunction, seq [l; r])
let inline Disjunction (l, r) = Gn (LDisjunction, seq [l; r])
let inline DisjunctSumForRange (var: string, upto: int, fml: GenericFormula<_, _, _>) =
  let xs =
    Seq.init upto (fun i ->
      fml |> map (map (Expression.subst var (Expression.constant (i+1))))
    ) |> Seq.cache
  Gn (LDisjunction, xs)
let inline DisjunctSumInSet    (var: string, xs, fml: GenericFormula<_, _, _>) =
  let xs =
    xs |> Seq.map (fun x ->
      fml |> map (map (Expression.subst var x))
    ) |> Seq.cache
  Gn (LDisjunction, xs)

[<Struct; StructuredFormatDisplay("{str}")>]
type QuantifierForallOrExists = QFEForall of fv:string | QFEExists of ev:string with 
  member this.var = match this with QFEForall x -> x | QFEExists x -> x
  member this.str =
    match this with QFEForall x -> sprintf "forall %s." x | QFEExists x -> sprintf "exists %s." x
  static member inline FilterFV (q: QuantifierForallOrExists, xs) =
    xs |> Seq.filter ((<>) q.var)
[<Struct; StructuredFormatDisplay("{str}")>]
type QuantifierExistsOrNotExists = QENExists of ev:string | QENNotExists of nv: string with
  member this.var = match this with QENExists x -> x | QENNotExists x -> x
  member this.str =
    match this with QENExists x -> sprintf "exists %s." x | QENNotExists x -> sprintf "not_exists %s." x
  static member inline FilterFV (q: QuantifierExistsOrNotExists, xs) =
    xs |> Seq.filter ((<>) q.var)
let inline varOfQuantifier (x: ^Q) =
  (^Q: (member var: string) x)

[<Struct; StructuredFormatDisplay("{str}")>]
type ComparisonOps = CompEq | CompLt | CompGt | CompLte | CompGte with
  member this.str =
    match this with CompEq -> "=" | CompLt -> "<" | CompGt -> ">" | CompLte -> "<=" | CompGte -> ">="
[<Struct; StructuredFormatDisplay("{str}")>]
type ComparisonLt = ComparisonLt with
  member this.str = "<"
  static member inline CompareBy (_, l, r) = Expression.lessThan (l, r)

///     Monad<'Matrix>, Foldable<'Quantifier>
[<StructuredFormatDisplay("{str}")>]
type PrenexForm<'Quantifier, 'Matrix> =
  | PFQuantifier of 'Quantifier * PrenexForm<'Quantifier, 'Matrix>
  | PFMatrix of 'Matrix
  with
    member this.str =
      match this with
        | PFQuantifier (q, p) -> sprintf "%A %A" q p
        | PFMatrix m -> sprintf "%A" m
    member this.matrix =
      match this with
        | PFMatrix m -> m
        | PFQuantifier (_, p) -> p.matrix
    static member inline FV x =
      let rec fv = function
        | PFQuantifier (q, p) -> fv p |> Seq.filter ((<>) (varOfQuantifier q))
        | PFMatrix m -> fvOf m
      fv x
    static member (>>=) (x, f) =
      match x with
        | PFMatrix x -> f x
        | PFQuantifier (q, pf) -> PFQuantifier (q, pf >>= f)
    static member inline Return x = PFMatrix x
    static member ToSeq x =
      match x with
        | PFQuantifier (q, x) -> Seq.append (Seq.singleton q) (toSeq x)
        | PFMatrix _ -> Seq.empty

///     Functor<'Term>, Foldable<'Term>, TruthValue, Tautology
[<Struct; StructuredFormatDisplay("{str}")>]
type NNFAtomicOrNegate<'Comparison, 'Term, 'Negatee> =
  | NNFAtomic of afm:AtomicFormula<'Comparison, 'Term>
  | NNFNegate of 'Negatee
  with
    member this.str =
      match this with NNFAtomic x -> sprintf "%A" x | NNFNegate n -> sprintf "~%A" n
    static member inline FV x =
      match x with
        | NNFAtomic a -> fvOf a
        | NNFNegate n -> fvOf n
    static member inline Map (x, f) =
      match x with
        | NNFAtomic a -> NNFAtomic (map f a)
        | NNFNegate n -> NNFNegate (map f n)
    static member inline ToSeq x =
      match x with
        | NNFAtomic a -> toSeq a
        | NNFNegate n -> toSeq n
    static member inline TruthValue b = NNFAtomic (truthValue b)
    static member inline IsTautology x =
      match x with
        | NNFAtomic a -> isTautology a
        | NNFNegate n -> isTautology n |> Option.map not
    static member inline Reduce x = x

[<Struct>]
type Empty = Empty with
  static member inline FilterFV (Empty, xs) = xs
  static member inline ReduceBy (Empty, _, x) = x

type NegationNormalForm<'Comparison, 'Term, 'Negatee> =
  GenericFormula<
    NNFAtomicOrNegate<'Comparison, 'Term, 'Negatee>,
    Empty,
    LogicalOp>

[<Struct; StructuredFormatDisplay("{str}")>]
type FormulaUnaryOp<'Quantifier> =
  | FQuantifier of 'Quantifier
  | FNegate
  with
    member this.str = match this with FQuantifier q -> sprintf "%A" q | FNegate -> "~"
    static member inline FilterFV (op, xs) =
      match op with
        | FQuantifier q -> xs |> filterFv q
        | _ -> xs

type FormulaBase<'Quantifier, 'Expr> =
  GenericFormula<
    AtomicFormula<ComparisonOps, 'Expr>,
    FormulaUnaryOp<'Quantifier>,
    LogicalOp>

type Formula<'Expr> = FormulaBase<QuantifierForallOrExists, 'Expr>

[<Struct; StructuredFormatDisplay("{str}")>]
type Negate = Negate 
  with 
    member this.str = "~"
    static member inline FilterFV (Negate, xs) = xs
    static member inline ReduceBy (Negate, cstr, x) =
      if x = truthValue true then truthValue false
      else if x = truthValue false then truthValue true
      else cstr x

type PrenexMatrix<'Expr> =
  GenericFormula<
    AtomicFormula<ComparisonOps, 'Expr>,
    Negate,
    LogicalOp>

type PrenexFormula<'Expr> =
  PrenexForm<
    QuantifierForallOrExists,
    PrenexMatrix<'Expr>>

type PrenexFormulaWithoutForall<'Expr> =
  PrenexForm<
    QuantifierExistsOrNotExists,
    PrenexMatrix<'Expr>>

type PrenexNNFMatrix<'Expr> =
  NegationNormalForm<
    ComparisonOps,
    'Expr,
    AtomicFormula<ComparisonOps, 'Expr>>

type PrenexNNFFormula<'Expr> =
  PrenexForm<
    QuantifierExistsOrNotExists,
    PrenexNNFMatrix<'Expr>>

type PrenexNNFLtMatrix<'Expr> =
  NegationNormalForm<
    ComparisonLt,
    'Expr,
    DivisibilityConstant<'Expr>>

type PrenexNNFLtFormula<'Expr> =
  PrenexForm<
    QuantifierExistsOrNotExists,
    PrenexNNFLtMatrix<'Expr>>
    
type EliminatedFormula<'Expr> =
  GenericFormula<
    PrenexNNFLtMatrix<'Expr>,
    Negate,
    LogicalOp>

