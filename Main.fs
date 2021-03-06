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

module PresburgerFs.Main
open PresburgerFs.Expr
open PresburgerFs.Formula
open PresburgerFs.Elimination
open PresburgerFs.Dsl
module Generic = FSharpPlus.Operators

#if DEBUG
let inline check fml =
  let inline show fml =
    printfn "<=> %A" fml
    fml
  printfn "    %A" fml
  fml |> toPrenexForm |> show
      |> eliminateForall |> show
      |> toNegationNormalForm |> show
      |> eliminateCompareOps |> show
      |> Generic.map reduce |> show
      |> removeDuplicatesInAtomic |> show
      |> normalizeAllCoefficientsToOne |> show
      |> eliminateQuantifiers |> show
      |> reduce |> show

PresburgerFs.Tests.run ()
#endif