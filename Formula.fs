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

module PresburgerFs.Formula
open PresburgerFs.Expr
open FSharpPlus

[<Struct; StructuredFormatDisplay("{str}")>]
type DivisibilityConstant<'Term> = {
  divisor:  nat
  dividend: 'Term
} with
  member this.str =
    sprintf "%A|%A" this.divisor this.dividend

[<Struct; StructuredFormatDisplay("{str}")>]
type AtomicFormula<'Comparison, 'Term> =
  | AFComparison   of cmp:'Comparison * lhs:'Term * rhs:'Term
  | AFDivisiblity  of DivisibilityConstant<'Term>
  | AFTrue | AFFalse
  with
    member this.str =
      match this with
        | AFTrue -> "T" | AFFalse -> "F"
        | AFDivisiblity d -> sprintf "%A" d
        | AFComparison (c, l, r) -> sprintf "%A %A %A" l c r

[<StructuredFormatDisplay("{str}")>]
type NegationNormalForm<'Negatee, 'Comparison, 'Term> =
  | NNFAtomic of AtomicFormula<'Comparison, 'Term>
  | NNFNegate of 'Negatee
  | NNFConjunction of NegationNormalForm<'Negatee, 'Comparison, 'Term> * NegationNormalForm<'Negatee, 'Comparison, 'Term> 
  | NNFDisjunction of NegationNormalForm<'Negatee, 'Comparison, 'Term> * NegationNormalForm<'Negatee, 'Comparison, 'Term>
  | NNFDisjunctSumForRange of string * upto:int       * NegationNormalForm<'Negatee, 'Comparison, 'Term> 
  | NNFDisjunctSumInSet    of string * set:'Term list * NegationNormalForm<'Negatee, 'Comparison, 'Term> 
  with
    member inline this.str =
      match this with
        | NNFAtomic a -> sprintf "%A" a
        | NNFNegate x -> sprintf "~%A" x
        | NNFConjunction (l, r) -> sprintf "(%A ^ %A)" l r
        | NNFDisjunction (l, r) -> sprintf "(%A v %A)" l r
        | NNFDisjunctSumForRange (v, u, x) -> 
          sprintf "V(%s = 1 to %i) %A" v u x
        | NNFDisjunctSumInSet    (v, s, x) ->
          sprintf "V(%s in { %s }) %A" v (s |> List.map (sprintf "%A") |> String.concat ", ") x

[<StructuredFormatDisplay("{str}")>]
type PropositionalFormula<'Comparison, 'Term> =
  | PAtomic of AtomicFormula<'Comparison, 'Term>
  | PConjunction of PropositionalFormula<'Comparison, 'Term> * PropositionalFormula<'Comparison, 'Term>
  | PDisjunction of PropositionalFormula<'Comparison, 'Term> * PropositionalFormula<'Comparison, 'Term>
  | PNegate of PropositionalFormula<'Comparison, 'Term>
  with
    member this.str =
      match this with
        | PAtomic a -> sprintf "%A" a
        | PNegate x -> sprintf "~%A" x
        | PConjunction (l, r) -> sprintf "(%A ^ %A)" l r
        | PDisjunction (l, r) -> sprintf "(%A v %A)" l r

[<StructuredFormatDisplay("{str}")>]
type PrenexForm<'Quantifier, 'Matrix> =
  | PFQuantifier of 'Quantifier * string * PrenexForm<'Quantifier, 'Matrix>
  | PFMatrix of 'Matrix
  with
    member this.str =
      match this with
        | PFQuantifier (q, v, p) -> sprintf "%A%s.%A" q v p
        | PFMatrix m -> sprintf "%A" m

[<StructuredFormatDisplay("{str}")>]
type Formula<'Quantifier, 'Comparison, 'Term> =
  | FmlAtomic of AtomicFormula<'Comparison, 'Term>
  | FmlConjunction of Formula<'Quantifier, 'Comparison, 'Term> * Formula<'Quantifier, 'Comparison, 'Term>
  | FmlDisjunction of Formula<'Quantifier, 'Comparison, 'Term> * Formula<'Quantifier, 'Comparison, 'Term>
  | FmlNegate of Formula<'Quantifier, 'Comparison, 'Term>
  | FmlQuantifier of 'Quantifier * string * Formula<'Quantifier, 'Comparison, 'Term>
  with
    member this.str =
      match this with
        | FmlAtomic a -> sprintf "%A" a
        | FmlNegate x -> sprintf "~%A" x
        | FmlConjunction (l, r) -> sprintf "(%A ^ %A)" l r
        | FmlDisjunction (l, r) -> sprintf "(%A v %A)" l r
        | FmlQuantifier (q, v, p) -> sprintf "%A%s.%A" q v p

[<Struct; StructuredFormatDisplay("{str}")>]
type QuantifierForallOrExists = QFEForall | QFEExists with 
  member this.str =
    match this with QFEForall -> "∀" | QFEExists -> "∃"
[<Struct; StructuredFormatDisplay("{str}")>]
type QuantifierExistsOrNotExists = QENExists | QENNotExists with
  member this.str =
    match this with QENExists -> "∃" | QENNotExists -> "~∃"

[<Struct; StructuredFormatDisplay("{str}")>]
type ComparisonOps = CompEq | CompLt | CompGt | CompLte | CompGte with
  member this.str =
    match this with CompEq -> "=" | CompLt -> "<" | CompGt -> ">" | CompLte -> "<=" | CompGte -> ">="
[<Struct; StructuredFormatDisplay("{str}")>]
type ComparisonLt = ComparisonLt with
  member this.str = "<"

type OriginFormula = Formula<QuantifierForallOrExists, ComparisonOps, Expr>
type OriginFormulaWithoutForall = Formula<QuantifierExistsOrNotExists, ComparisonOps, Expr>

type PrenexFormula =
  PrenexForm<
    QuantifierExistsOrNotExists,
    PropositionalFormula<ComparisonOps, Expr>>

type PrenexNNFFormula =
  PrenexForm<
    QuantifierExistsOrNotExists,
    NegationNormalForm<
      AtomicFormula<ComparisonOps, Expr>,
      ComparisonOps,
      Expr>>

type QuantifierFreeFormula =
  NegationNormalForm<DivisibilityConstant<Expr>, ComparisonLt, Expr>

type PrenexNNFLtFormula =
  PrenexForm<
    QuantifierExistsOrNotExists,
    QuantifierFreeFormula>

// Monad<'Matrix>,
// Foldable<'Quantifier * string>
type PrenexForm<'Quantifier, 'Matrix> with
  static member Return x = PFMatrix x
  static member (>>=) (x, f) =
    match x with
      | PFMatrix mx -> f mx
      | PFQuantifier (q, v, s) -> PFQuantifier (q, v, s >>= f)
  static member ToSeq x =
    match x with
      | PFMatrix _ -> Seq.empty
      | PFQuantifier (q, v, s) -> seq { yield (q, v); yield! toSeq s }

// Functor<'Term>,
// Foldable<Choice<'Term, 'Comparison * 'Term * 'Term>>
type DivisibilityConstant<'Term> with
  static member Map (x: DivisibilityConstant<_>, f) =
    { divisor = x.divisor; dividend = f x.dividend }
  static member ToSeq (x: DivisibilityConstant<_>) =
    Seq.singleton <| Choice1Of2 x.dividend

// Bifunctor<'Term, 'Comparison * 'Term * 'Term>,
// Foldable<Choice<'Term, 'Comparison * 'Term * 'Term>>
type AtomicFormula<'Comparison, 'Term> with  
  static member Bimap (x: AtomicFormula<_, _>, f, g) =
    match x with
      | AFComparison (c, l, r) -> (c, f l, f r) |> g |> AFComparison
      | AFDivisiblity d -> d |> map f |> AFDivisiblity
      | AFFalse -> AFFalse | AFTrue -> AFTrue
  static member ToSeq (x: AtomicFormula<_, _>) =
      match x with
        | AFComparison (c, l, r) -> seq [ Choice1Of2 l; Choice1Of2 r; Choice2Of2 (c, l, r)]
        | AFDivisiblity d -> toSeq d
        | _ -> Seq.empty

// Bifunctor<AtomicFormula<_, _>, 'Negatee>,
// Bifunctor<'Term, 'Comparison * 'Term * 'Term>,
// Foldable<Choice<'Term, 'Comparison * 'Term * 'Term>>
type NegationNormalForm<'Negatee, 'Comparison, 'Term> with
  static member Bimap (x: NegationNormalForm<_, _, _>, f, g) =
    match x with
      | NNFAtomic a -> NNFAtomic (f a)
      | NNFNegate n -> NNFNegate (g n)
      | NNFConjunction (l, r) -> NNFConjunction (bimap f g l, bimap f g r)
      | NNFDisjunction (l, r) -> NNFDisjunction (bimap f g l, bimap f g r)
      | NNFDisjunctSumForRange (v, u, n) -> NNFDisjunctSumForRange (v, u, bimap f g n)
      | NNFDisjunctSumInSet    (v, s, n) -> NNFDisjunctSumInSet    (v, s, bimap f g n)

  static member Bimap (x: QuantifierFreeFormula, f, g) =
    match x with
      | NNFAtomic a -> a |> bimap f g |> NNFAtomic
      | NNFNegate n -> n |> map f |> NNFNegate
      | NNFConjunction (l, r) -> NNFConjunction (bimap f g l, bimap f g r)
      | NNFDisjunction (l, r) -> NNFDisjunction (bimap f g l, bimap f g r)
      | NNFDisjunctSumForRange (v, u, n) -> NNFDisjunctSumForRange (v, u, bimap f g n)
      | NNFDisjunctSumInSet    (v, s, n) -> NNFDisjunctSumInSet    (v, s |> List.map f, bimap f g n)
  
  static member ToSeq (x: QuantifierFreeFormula) =
    match x with
      | NNFAtomic a -> toSeq a | NNFNegate n -> toSeq n
      | NNFConjunction (l, r) | NNFDisjunction (l, r) -> Seq.append (toSeq l) (toSeq r)
      | NNFDisjunctSumForRange (v, u, n) ->
        let xs = toSeq n
        seq {
          for x in xs do
            match x with
              | Choice1Of2 e when e |> Expr.contains v ->
                for i = 1 to u do
                  yield e |> Expr.subst v (ENum i) |> Choice1Of2
              | Choice2Of2 (c, l, r) when l |> Expr.contains v && r |> Expr.contains v ->
                for i = 1 to u do
                for j = 1 to u do
                  yield Choice2Of2 (c, l |> Expr.subst v (ENum i), r |> Expr.subst v (ENum j))
              | Choice2Of2 (c, l, r) when l |> Expr.contains v ->
                for i = 1 to u do
                  yield Choice2Of2 (c, l |> Expr.subst v (ENum i), r)
              | Choice2Of2 (c, l, r) when r |> Expr.contains v ->
                for i = 1 to u do
                  yield Choice2Of2 (c, l, r |> Expr.subst v (ENum i))
              | x -> yield x
        }
      | NNFDisjunctSumInSet (v, ss, n) ->
        let xs = toSeq n
        seq {
          for x in xs do
            match x with
              | Choice1Of2 e when e |> Expr.contains v ->
                for s in ss do
                  yield e |> Expr.subst v s |> Choice1Of2
              | Choice2Of2 (c, l, r) when l |> Expr.contains v && r |> Expr.contains v ->
                for s in ss do
                for t in ss do
                  yield Choice2Of2 (c, l |> Expr.subst v s, r |> Expr.subst v t)
              | Choice2Of2 (c, l, r) when l |> Expr.contains v ->
                for s in ss do
                  yield Choice2Of2 (c, l |> Expr.subst v s, r)
              | Choice2Of2 (c, l, r) when r |> Expr.contains v ->
                for s in ss do
                  yield Choice2Of2 (c, l, r |> Expr.subst v s)
              | x -> yield x
        }
