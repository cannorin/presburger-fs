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

module PresburgerFs.Dsl
open PresburgerFs.Expr
open PresburgerFs.Formula

let inline var x = EVar x
let inline num n = ENum n
let inline ( ^< ) e f  : Formula<Expr> = G0 (AFComparison (CompLt, e, f))
let inline ( ^> ) e f  : Formula<Expr> = G0 (AFComparison (CompGt, e, f))
let inline ( ^= ) e f  : Formula<Expr> = G0 (AFComparison (CompEq, e, f))
let inline ( ^<= ) e f : Formula<Expr> = G0 (AFComparison (CompLte, e, f))
let inline ( ^>= ) e f : Formula<Expr> = G0 (AFComparison (CompGte, e, f))
let inline ( ^% )  n e : Formula<Expr> = G0 (AFDivisiblity { divisor = n; dividend = e})
let inline (&.) f g  : Formula<Expr> = Conjunction (f, g)
let inline (|.) f g  : Formula<Expr> = Disjunction (f, g)
let inline not' x    : Formula<Expr> = G1 (FNegate, x)
let inline ands (xs: #seq<_>) : Formula<Expr> = Gn (LConjunction, xs)
let inline ors  (xs: #seq<_>) : Formula<Expr> = Gn (LDisjunction, xs)
let inline forall vs x : Formula<Expr> =
  vs |> Seq.rev
     |> Seq.fold (fun state v -> G1 (FQuantifier (QFEForall v), state)) x
let inline exists vs x : Formula<Expr> =
  vs |> Seq.rev
     |> Seq.fold (fun state v -> G1 (FQuantifier (QFEExists v), state)) x

#if DEBUG
let examples = [
  exists ["x"] (
    (3 * var "x" ^< num 9  |. 7 * var "x" - num 6 ^> num 7)
    &. 2u ^% var "x"
  );

  forall ["x"] (
    exists ["y"] (
      var "x" ^= 2 * var "y" |. var "x" ^= 2 * var "y" + num 1
  ));

  forall ["x"; "z"] (
    exists ["y"] (
      var "x" + var "y" ^> var "z"
    )
  );

  forall ["x"] (
       var "x" ^= num 0
    |. forall ["y"] (
         not' (var "x" + var "y" ^= var "y")
       )
  );
]
#endif