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
[<AutoOpen>]
module PresburgerFs.Debug

#if DEBUG
let sw = System.Diagnostics.Stopwatch()
#endif
let inline startClock () =
#if DEBUG
  sw.Stop()
  sw.Reset()
  sw.Start()
#endif
  ()
let inline check msg x =
#if DEBUG
  let es = sw.ElapsedMilliseconds
  if es > 100L then
    printfn "%s: %ims" msg es
  startClock()
#endif
  x