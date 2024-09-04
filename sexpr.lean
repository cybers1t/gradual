/- 
Copyright (c) 2018 Cybers1t. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Cybers1t

An s-expression parser, printer, and syntax
-/

namespace Sexpr

inductive Sexp (α : Type)
| list (xs : Array (Sexp α))
| arg (x : α)

open Lean Std in
partial def Sexp.reprPrec [Repr α] (x : Sexp α) (n : Nat) : Format :=
  match x with
  | .arg x => repr x
  | .list xs => "(" ++ (Format.joinSep (xs.toList.map (fun x => Sexp.reprPrec x n)) " ") ++ ")"

open Lean Std in
instance [Repr α] : Repr (Sexp α) where 
  reprPrec := Sexp.reprPrec

end Sexpr

