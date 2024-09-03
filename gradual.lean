import Lean
open Lean 
-- Gradual Typing for Functional Languages: http://scheme2006.cs.uchicago.edu/13-siek.pdf

namespace Gradual

/-- Set of Runtime kinds -/
inductive RuntimeTy | int | bool
deriving DecidableEq, Inhabited


/-- Runtime kinds to Lean types -/
def RuntimeTy.denote : RuntimeTy → Type 
| int => Int
| bool => Bool

/-- Types tracked by the type system -/
inductive Ty
| static (k : RuntimeTy)
| dyn
| arr (i o : Ty)
deriving DecidableEq, Inhabited, Repr

  -- (a -> (b -> c)) ~= a -> b -> c
  -- (a -> (b -> (c -> d)) ~= a -> b -> c -> d
  -- ((a -> b) -> c) ~= (a -> b) -> c
  def Ty.toString (isLeftOfArr: Bool := false) : Ty → String
  | .static .int => "int"
  | .static .bool => "bool"
  | .dyn => "⋆"
  | .arr i o => 
     let str := s!"{i.toString true} → {o.toString false}"
     if isLeftOfArr then s!"({str})" else str

instance : ToString Ty where
  toString := Ty.toString

instance : Coe RuntimeTy Ty where coe := .static

def Ty.bool : Ty := ↑RuntimeTy.bool
def Ty.int : Ty := ↑RuntimeTy.int

-- ordering is by set denotation, so .dyn is top since it holds the largest number of values.
def Ty.related : Ty → Ty → Bool 
| _, .dyn => true
| .arr a b, .arr a' b' => a.related a' && b.related b'
| .static x, .static y => x = y
| x, y => x == y

theorem Ty.related_refl : Ty.related x x := by
  induction x
  · simp [related]
  · simp [related]
  · simp [*, related]

abbrev BVarId := UInt32
abbrev FVarId := String

inductive Expr 
| bool (b: Bool)
| int (i : Int)
| bvar (i : BVarId) -- de bruijn indexed variables.
| lam (i : Ty := .dyn) (e : Expr) -- lambda
| app (f x : Expr) -- function application
| cast (e : Expr) (t : Ty) -- `cast e to t`.
deriving DecidableEq, Inhabited, Repr

structure Toplevel where
  defs : HashMap FVarId Expr  -- toplevel function definitions.

namespace CastInsertion
inductive Error where
| invalidFnArgTy (f : Expr) (x : Expr) (tExpected: Ty) (tFound : Ty)
| expectedArrTyForApp (f : Expr) (tFound : Ty)
| invalidCast (e : Expr) (eTy : Ty) (expectedTy : Ty)
| unexpectedCastInSurfaceLang (e : Expr) (eTy : Ty)


structure State where 
  errors : Array Error

abbrev GradualM (α : Type) : Type := StateT State IO α

namespace GradualM

def lookupBvarTy (i : BVarId) : GradualM Ty := sorry
def withBVarTy (ty : Ty) (k : GradualM α) : GradualM α := sorry
def lookupFvarTy (i : FVarId) : GradualM Ty := sorry
def addBvar (t : Ty) (k : BVarId → GradualM α) : GradualM α := sorry
def logError (e : Error) : GradualM Unit := do
  modify fun s => { s with errors := s.errors.push e }

def throw (e : Error) (a : α) : GradualM α := do
  logError e
  return a

-- | See that this function is a mix of type inference and cast insertion
def cast (e : Expr) : GradualM (Expr × Ty) := 
  match e with
  | Expr.bool _ => return (e, .bool)
  | Expr.int _ => return (e, .int)
  | Expr.cast e t => 
    throw (.unexpectedCastInSurfaceLang e t) (e, t)
  | .bvar i => return (e, ← lookupBvarTy i) -- CVAR
  | .lam it ebody => do -- CLAM
     let (ebody, ot) ← withBVarTy it (cast ebody)
     return (.lam it ebody, .arr it ot)
  |.app f x => do
      let (ef, tf) ← cast f 
      match tf with
      | .dyn => 
        let (ex, tx) ← cast x
        let ef := Expr.cast ef (.arr tx .dyn)
        return (.app ef ex, .dyn) -- CAPP1
      | .arr ti to => 
          let (ex, tx) ← cast x
          if ti = to then -- CAPP3
            return (.app ef ex, to) 
          else if ti.related tx then  -- CAPP 2
            return (.app ef (.cast ex ti), to)
          else -- error 
            throw (.invalidFnArgTy f x ti tx) (.app ef ex, to)
       | _ => throw (.expectedArrTyForApp ef tf) (.app ef x, .dyn)

end GradualM
end CastInsertion


namespace Eval


inductive Evaluable
| bool (b : Bool)
| int (i : Int)
| bvar (i : BVarId)
| lam (ity : Ty) (body : Expr)

inductive SimpleVal
| int (i : Int)
| bool (b : Bool)
| lam (i : Ty) (e : Expr)
deriving DecidableEq, Repr



/-- Expression contexts, in the fine grained call by value style -/
inductive ExprCtx 
| evalArg (f : Expr) 
| evalFn (x : SimpleVal) -- [f] v
| evalCast  (t : Ty)

abbrev Error := String

structure State where
  cur? : Expr ⊕ SimpleVal
  stack : List (ExprCtx ) -- current continuation
  error? : Option String
  finalVal? : Option SimpleVal

def State.setErr (s : State) (e : Error)  : State :=
  { s with error? := .some e }

abbrev EvalM := StateT State IO

inductive Result (ε α : Type)
| ok (a : α)
| err (e : ε)

def SimpleVal.toExpr : SimpleVal → Expr 
| .int i => .int i
| .bool b => .bool b
| .lam i b => .lam i b

instance : ToString SimpleVal where
  toString v := Format.pretty <| repr v
  

def subst (body : Expr) (val : Expr) : Expr := 
  match body with
  | .bool b => .bool b
  | .int i => .int i
  | .bvar i => if i = 0 then val else .bvar (i - 1)
  | .lam i b => .lam i (subst b val)
  | .app f x => .app (subst f val) (subst x val)
  | .cast e ty => .cast (subst e val) ty

def SimpleVal.tryCast? (v : SimpleVal) (t : Ty) : Error ⊕ SimpleVal :=
  match (v, t) with
  | (.int v, .static .int) => .inr <| .int v
  | (.int v, .dyn) => .inr <| .int v
  | (.int v, _) => .inl <| s!"expected int/dyn cast for value {v}, found cast to {t}"
  | (.bool b, .static .bool) => .inr <| .bool b
  | (.bool b, .dyn) => .inr <| .bool b
  -- | TODO: how to typecheck this, mofos?
  | (.bool b, _) => .inl <| s!"expected int/dyn cast for value {v}, found cast to {t}"
  | (.lam i body, .dyn) => .inr <| .lam i body
  -- | TODO: how to typecheck this, mofos?
  | (.lam i body, .arr _ai _ao) => .inr <| .lam i body -- TODO:
  -- | TODO: how to typecheck this, mofos?
  | (.lam _i _body, _) => .inl <| s!"expected int/dyn cast for value {v}, found cast to {t}"    

def evalCur : EvalM Unit := do
  -- don't proceed to evaluate in case we have an error.
  if let .some _ := (← get).error? then return ()
  match (← get).cur? with
  | .inl expr => 
     match expr with
     | .bool b => modify fun s => { s with cur? := .inr <| .bool b }
     | .int i => modify fun s => { s with cur? := .inr <| .int i }
     | .bvar _ => modify fun s => { s with error? := "found illegal bvar {expr}" }
     | .lam i e => modify fun s => { s with cur? := .inr <| .lam i e } 
     | .app f x => modify fun s => { s with cur? := .inl x, stack := .evalArg f :: s.stack }
     | .cast e t => modify fun s => { s with cur? := .inl e, stack := .evalCast t :: s.stack }
  | .inr val => 
      -- | TODO: write a `pop` fun.
      match (← get).stack with
      | [] => modify fun s => { s with finalVal? := val, stack := s.stack }
      | k :: ks => 
         match k with
         | .evalArg f  => modify fun s => { s with cur? := .inl f, stack := .evalFn val :: ks }
         | .evalFn rhs => 
           match val with
           | .lam _ body =>
              modify fun s => { s with cur? := .inl <| subst body rhs.toExpr, stack := ks }
           | _ => modify fun s => { s with error? := "expected lambda, found non-lambda on the stack" }
         | .evalCast t =>
             match val.tryCast? t with
             | .inl e => modify fun s => { s with error? := .some e }
             | .inr v => modify fun s => { s with cur? := .inr v, stack := ks } 
end Eval
end Gradual
def foo : IO Unit := return ()
