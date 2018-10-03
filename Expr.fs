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

module PresburgerFs.Expr
open FSharp.Collections

type countmap<'a, 'num when 'a: comparison> = Map<'a, 'num>

module CountMap =
  let inline singleton x = Map.ofSeq [(x, one)]
  let inline count x xs = xs |> Map.tryFind x ?| zero
  let inline contains x xs = count x xs <> zero
  let inline isEmpty xs = Map.forall (fun _ -> ((=) 0)) xs
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
  let inline toSeq xs = Map.toSeq xs |> Seq.filter (snd >> (<>) 0)

[<Struct; StructuredFormatDisplay("{str}")>]
type Expr = Expr of int * countmap<string, int>
  with
    member x.str =
      let s =
        let xs = match x with Expr (_, v) -> v
        xs |> Map.toSeq
           |> Seq.map (fun (s, n) -> sprintf "%i*%s" n s)
           |> String.concat " + "
      match x with
        | Expr (0, xs) when xs |> Map.isEmpty |> not -> s
        | Expr (n, xs) when xs |> Map.isEmpty |> not -> sprintf "%s + %i" s n
        | Expr (n, _) -> sprintf "%i" n
    override x.ToString() = x.str
    static member (+) (Expr (nx, xs), Expr (ny, ys)) =
      Expr (nx + ny, CountMap.union xs ys)
    static member (-) (Expr (nx, xs), Expr (ny, ys)) =
      Expr (nx - ny, CountMap.substract xs ys)
    static member (*) (Expr (nx, xs), n: int) =
      if n = 0 then Expr (0, Map.empty)
      else          Expr (nx * n, xs |> Map.map (fun _ -> (*) n))
    static member (*) (n: int, x: Expr) = Expr.(*) (x, n)

module Expr =
  let inline count vn (Expr (_, cm)) = cm |> CountMap.count vn
  let inline contains vn (Expr (_, cm)) = cm |> CountMap.contains vn
  let inline num (Expr (n, _)) = n
  let inline vars (Expr (_, cm)) = cm

  ///       e |> subst "x" v 
  ///     = e[x := v]
  let subst var (value: Expr) (Expr (n, vars)) =
    if n = 0 && vars |> CountMap.isEmpty then
      Expr (n, vars |> Map.remove var)
    else
      let vc = vars |> CountMap.count var
      let vars' = vars |> Map.remove var
      Expr (n, vars') + vc * value

let inline EVar name = Expr (0, CountMap.singleton name)
let inline ENum num  = Expr (num, Map.empty)

