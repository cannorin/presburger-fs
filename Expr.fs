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

module PresburgerFs.Expr
open FSharp.Collections
open System

type countmap<'a, 'num when 'a: comparison> = Map<'a, 'num>

module CountMap =
  let inline normalize xs = xs |> Map.filter (fun _ v -> v <> zero)
  let inline singleton x = Map.ofSeq [(x, one)]
  let inline count x xs = xs |> Map.tryFind x ?| zero
  let inline contains x xs = count x xs <> zero
  let inline isEmpty xs = Map.forall (fun _ -> ((=) zero)) xs
  let inline isSubsetOf big small =
    seq {
      for KVP (k, v) in small do
        let bc = big |> count k
        yield v <= bc
    } |> Seq.forall id
  let inline add    x xs = xs |> Map.add x (succ <| count x xs)
  let inline remove x xs = xs |> Map.add x (pred <| count x xs)
  let inline union xs ys =
    let mutable cs = xs
    for KVP (k, v) in ys do
      match cs |> Map.tryFind k with
        | Some value ->
          cs <- cs |> Map.add k (v + value)
        | None ->
          cs <- cs |> Map.add k v
    cs
  let inline substract xs ys =
    let mutable cs = xs
    for KVP (k, v) in ys do
      match cs |> Map.tryFind k with
        | Some value ->
          cs <- cs |> Map.add k (value - v)
        | None ->
          cs <- cs |> Map.add k (zero - v)
    cs
  let inline ofSeq xs =
    let mutable cs = Map.empty
    for x in xs do
      match cs |> Map.tryFind x with
        | Some value ->
          cs <- cs |> Map.add x (succ value)
        | None ->
          cs <- cs |> Map.add x zero
    cs
  let inline toSeq xs = Map.toSeq xs |> Seq.filter (snd >> (<>) zero)

module Expression =
  let inline isConstant (a: ^A) =
    (^A: (static member isConstant: ^A -> int option) a)
  let inline constant n : ^A =
    (^A: (static member constant: int -> ^A) n)
  let inline variable n : ^A =
    (^A : (static member variable: string -> ^A) n)
  let inline subst x (b: ^A) (a: ^A) : ^A =
    (^A: (static member subst: ^A * string * ^A -> ^A) a,x,b)
  let inline count var (a: ^A) =
    (^A: (static member count: ^A * string -> int) a,var)
  let inline contains   var (a: ^A) =
    count var a <> 0
  let inline lessThan (a: ^A, b: ^A) =
    (^A: (static member lessThan: ^A * ^A -> bool option) a,b)
  let inline multiply (i: int) (a: ^A) =
    (^A: (static member multiply: ^A * int -> ^A) a,i)
  let inline remove v a = a |> subst v (constant 0)

[<Struct; StructuredFormatDisplay("{str}")>]
type Expr = 
  | Expr of int * countmap<string, int>
  with
    member x.str =
      let s =
        let xs = match x with Expr (_, v) -> v
        xs |> CountMap.toSeq
           |> Seq.map (function 
                | (s, 1)  -> s
                | (s, -1) -> sprintf "-%s" s 
                | (s, n)  -> sprintf "%i%s" n s
              )
           |> String.concat " + "
      match x with
        | Expr (0, xs) when xs |> CountMap.isEmpty |> not -> s
        | Expr (n, xs) when xs |> CountMap.isEmpty |> not -> sprintf "%s + %A" s n
        | Expr (n, _) -> sprintf "%i" n
    static member inline (+) (Expr (nx, xs), Expr (ny, ys)) =
      Expr (nx + ny, CountMap.union xs ys)
    static member inline (-) (Expr (nx, xs), Expr (ny, ys)) =
      Expr (nx - ny, CountMap.substract xs ys)
    static member inline (*) (n, Expr (nx, xs)) =
      if n = zero then Expr (zero, Map.empty)
      else             Expr (nx * n, xs |> Map.map (fun _ -> (*) n))
    static member inline (*) (Expr (nx, xs), n) =
      if n = zero then Expr (zero, Map.empty)
      else             Expr (nx * n, xs |> Map.map (fun _ -> (*) n))
    static member inline Zero = Expr (zero, Map.empty)

    static member inline count (Expr (_, cm), vn) = cm |> CountMap.count vn
    ///       e |> subst "x" v 
    ///     = e[x := v]
    static member inline subst (Expr (n, vars), var, value: Expr) =
      if n = zero && vars |> CountMap.isEmpty then
        Expr (n, vars |> Map.remove var)
      else
        let vc = vars |> CountMap.count var
        let vars' = vars |> Map.remove var
        Expr (n, vars') + vc * value
    static member inline constant n = Expr (n, Map.empty)
    static member inline variable n = Expr (0, CountMap.singleton n)
    static member inline isConstant (Expr (n, vars)) = if CountMap.isEmpty vars then Some n else None
    static member inline lessThan (Expr (ln, lvars), Expr (rn, rvars)) =
      if CountMap.normalize lvars = CountMap.normalize rvars then
        if ln < rn then Some true
        else Some false
      else None
    static member inline multiply (a: Expr, i: int) = a * i
    static member inline FV (Expr (_, vars)) = vars |> CountMap.toSeq |> Seq.map fst |> Set.ofSeq

let inline EVar name = Expr (zero, CountMap.singleton name)
let inline ENum num  = Expr (num, Map.empty)

