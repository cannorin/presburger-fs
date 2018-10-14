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

let inline isTautology (fml: ^X) =
  (^X: (static member IsTautology: ^X -> bool option) fml)

let inline isTautologyWhen cond (fml: ^X) =
  (^X: (static member IsTautologyWhen: ^X * _ -> bool option) fml,cond)

let inline compareBy (cmp: ^Cmp) x y =
  (^Cmp: (static member CompareBy: ^Cmp * _ * _ -> bool option) cmp,x,y)

let inline AtomicTrue (_: ty< ^A >) =
  (^A: (static member AtomicTrue: ^A)())

let inline AtomicFalse (_: ty< ^A >) =
  (^A: (static member AtomicFalse: ^A)())

///     Bifunctor<nat, 'Term>, Foldable<'Term>, Tautology
[<Struct; StructuredFormatDisplay("{str}")>]
type DivisibilityConstant<'Term> = {
  divisor:  nat
  dividend: 'Term
} with
  member this.str =
    sprintf "%A|%A" this.divisor this.dividend
  static member Bimap (x, f, g) =
    { divisor = f x.divisor; dividend = g x.dividend }
  static member ToSeq x = seq [x.dividend]
  static member inline IsTautology x =
    Expression.isConstant x.dividend 
      |> Option.map (fun n -> n % int x.divisor = 0)

///     Functor<'Term>, Foldable<'Term>, Atomic, Tautology
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
    static member AtomicTrue  : AtomicFormula<'Comparison, 'Term> = AFTrue
    static member AtomicFalse : AtomicFormula<'Comparison, 'Term> = AFFalse

///     Monad<'G0>, Foldable<'G0>, Tautology
[<StructuredFormatDisplay("{str}")>]
type GenericFormula<'G0, 'G1, 'Gn> =
  | G0 of 'G0
  | G1 of 'G1 * GenericFormula<'G0, 'G1, 'Gn>
  | Gn of 'Gn * GenericFormula<'G0, 'G1, 'Gn> seq
  with
    member this.str =
      match this with
        | G0 x -> sprintf "%A"x 
        | G1 (o, x) -> sprintf "%A %A" o x
        | Gn (n, xs) -> 
          xs |> Seq.map (sprintf "%A") |> String.concat (sprintf "%A" n) |> sprintf "(%s)"
    static member (>>=) (x, f) =
      let rec bind = function
        | G0 x -> f x
        | G1 (o, x) -> G1 (o, bind x)
        | Gn (n, xs) -> Gn (n, xs |> Seq.map bind)
      bind x
    static member Return x = G0 x 
    static member ToSeq x =
      let rec ts = function
        | G0 x -> Seq.singleton x
        | G1 (_, x) -> toSeq x
        | Gn (_, xs) -> xs |> Seq.map toSeq |> Seq.concat
      ts x
    static member inline IsTautology x =
      let rec it = function
        | G0 x -> isTautology x
        | G1 (o, x)  -> o |> isTautologyWhen (it x)
        | Gn (n, xs) -> n |> isTautologyWhen (xs |> Seq.map it)
      it x

///     TautologyWhen
[<Struct; StructuredFormatDisplay("{str}")>]
type LogicalOp = LConjunction | LDisjunction
  with
    member this.str = match this with LConjunction -> " ^ " | LDisjunction -> " v "
    static member IsTautologyWhen (op, xs: bool option seq) =
      let xs = xs |> Seq.cache
      match op with
        | LConjunction ->
          if xs |> Seq.exists ((=) (Some false)) then Some false
          else if xs |> Seq.forall ((=) (Some true)) then Some true
          else None
        | LDisjunction ->
          if xs |> Seq.exists ((=) (Some true)) then Some true
          else if xs |> Seq.forall ((=) (Some false)) then Some false
          else None

let inline Conjunction (l, r) = Gn (LConjunction, seq [l; r])
let inline Disjunction (l, r) = Gn (LDisjunction, seq [l; r])
let inline DisjunctSumForRange (var: string, upto: int, fml: GenericFormula<_, _, _>) =
  let xs = seq {
    for i = 1 to upto do
      yield fml |> map (map (Expression.subst var (Expression.constant i)))
  }
  Gn (LDisjunction, xs)
let inline DisjunctSumInSet    (var: string, xs, fml: GenericFormula<_, _, _>) =
  let xs = seq {
    for x in xs do
      yield fml |> map (map (Expression.subst var x))
  }
  Gn (LDisjunction, xs)

let inline reduce (fml: GenericFormula< ^a, ^b, ^c >) : GenericFormula< ^a, ^b, ^c > =
  let inline mapTruth x =
    x |> Option.map (function true -> AtomicTrue ty<_> | false -> AtomicFalse ty<_>) 
  let rec r = function
    | G0 a -> G0 (isTautology a |> mapTruth ?| a)
    | G1 (x, y) ->
      let g1 = G1 (x, r y)
      isTautology g1 |> mapTruth |> Option.map G0 ?| g1
    | Gn (n, xs) ->
      let gn = Gn (n, xs |> Seq.map r)
      isTautology gn |> mapTruth |> Option.map G0 ?| gn
  r fml

[<Struct; StructuredFormatDisplay("{str}")>]
type QuantifierForallOrExists = QFEForall of fv:string | QFEExists of ev:string with 
  member this.var = match this with QFEForall x -> x | QFEExists x -> x
  member this.str =
    match this with QFEForall x -> sprintf "∀%s. " x | QFEExists x -> sprintf "∃%s. " x
[<Struct; StructuredFormatDisplay("{str}")>]
type QuantifierExistsOrNotExists = QENExists of ev:string | QENNotExists of nv: string with
  member this.var = match this with QENExists x -> x | QENNotExists x -> x
  member this.str =
    match this with QENExists x -> sprintf "∃%s. " x | QENNotExists x -> sprintf "~∃%s. " x
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
        | PFQuantifier (q, p) -> sprintf "%A%A" q p
        | PFMatrix m -> sprintf "%A" m
    static member (>>=) (x, f) =
      match x with
        | PFMatrix x -> f x
        | PFQuantifier (q, pf) -> PFQuantifier (q, pf >>= f)
    static member Return x = PFMatrix x
    static member ToSeq x =
      match x with
        | PFQuantifier (q, x) -> Seq.append (Seq.singleton q) (toSeq x)
        | PFMatrix _ -> Seq.empty

///     Functor<'Term>, Foldable<'Term>, Atomic, Tautology
[<Struct; StructuredFormatDisplay("{str}")>]
type NNFAtomicOrNegate<'Comparison, 'Term, 'Negatee> =
  | NNFAtomic of afm:AtomicFormula<'Comparison, 'Term>
  | NNFNegate of 'Negatee
  with
    member this.str =
      match this with NNFAtomic x -> sprintf "%A" x | NNFNegate n -> sprintf "%A" n
    static member inline Map (x, f) =
      match x with
        | NNFAtomic a -> NNFAtomic (map f a)
        | NNFNegate n -> NNFNegate (map f n)
    static member inline ToSeq x =
      match x with
        | NNFAtomic a -> toSeq a
        | NNFNegate n -> toSeq n
    static member AtomicTrue  : NNFAtomicOrNegate<'Comparison, 'Term, 'Negatee> = NNFAtomic AFTrue
    static member AtomicFalse : NNFAtomicOrNegate<'Comparison, 'Term, 'Negatee> = NNFAtomic AFFalse
    static member inline IsTautology x =
      match x with
        | NNFAtomic a -> isTautology a
        | NNFNegate n -> isTautology n |> Option.map not

///     TautologyWhen
[<Struct>]
type Empty = Empty with
  static member inline IsTautologyWhen (Empty, x: bool option) = x

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

type FormulaBase<'Quantifier, 'Expr> =
  GenericFormula<
    AtomicFormula<ComparisonOps, 'Expr>,
    FormulaUnaryOp<'Quantifier>,
    LogicalOp>

type Formula<'Expr> = FormulaBase<QuantifierForallOrExists, 'Expr>

type FormulaWithoutForall<'Expr> = FormulaBase<QuantifierExistsOrNotExists, 'Expr>

///     TautologyWhen
[<Struct; StructuredFormatDisplay("{str}")>]
type Negate = Negate 
  with 
    member this.str = "~"
    static member inline IsTautologyWhen (Negate, x) = x |> Option.map not

type PrenexMatrix<'Expr> =
  GenericFormula<
    AtomicFormula<ComparisonOps, 'Expr>,
    Negate,
    LogicalOp>

type PrenexFormula<'Expr> =
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

