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
deriving DecidableEq, Inhabited

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
| fvar (name : FVarId) -- free variables.
| lam (i : Ty := .dyn) (e : Expr) -- lambda
| app (f x : Expr) -- function application
| cast (e : Expr) (t : Ty) -- `cast e to t`.
deriving DecidableEq, Inhabited

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
  | Expr.fvar f => return (e, ← lookupFvarTy f)
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

/-- Expression contexts, in the fine grained call by value style -/
inductive ExprCtx (α : Type)
| appArg (f : Expr) (x : ExprCtx α) -- f [x]
| appFn (f : ExprCtx α) (x : α) -- [f] v
| castEnter (e : ExprCtx α) (t : Ty)
| castExit (x : α)
| hole (a : α) : ExprCtx α

inductive Evaluable
| bool (b : Bool)
| int (i : Int)
| bvar (i : BVarId)
| fvar (i : FVarId)
| lam (ity : Ty) (body : Expr)


/-- Convert an expression into an expression context to be evaluated -/
def Expr.startEvaluation : Expr → ExprCtx Evaluable
| .bool b => .hole (.bool b)
| .int i => .hole (.int i)
| .bvar i => .hole (.bvar i)
| .fvar i => .hole (.fvar i)
| .lam i body => .hole (.lam i body)
| .app f x => .appArg f (Expr.startEvaluation x)
| .cast e t => .castEnter (Expr.startEvaluation e) t

inductive SimpleVal
| int (i : Int)
| bool (b : Bool)
| cls (e : List (BVarId × SimpleVal)) -- can't use a hashmap because Lean kernel is a wimp.

def Evaluable.Evaluate : Evaluable → SimpleVal
| .int i => .int i
| .bool b => .bool b 
| .bvar i => sorry 
| .fvar f => sorry 

inductive Error
| invalidUnbox (v : SimpleVal × Ty) (expected : Ty)
| stackEmptyForValue
| stackStillHasContinuations

structure State where
  cur : Evaluable
  stack : List (ExprCtx Unit) -- current continuation
  error? : Option Error -- error.
  val? : Option Val -- evaluated value.

def State.setErr (s : State) (e : Error)  : State :=
  { s with error? := .some e }

abbrev EvalM : Type → Type := IO

structure Val where
  cast? : Option Ty
  val : SimpleVal

def Val.ofSimpleVal (val : SimpleVal) : Val := { cast? := none, val := val }

instance : Coe SimpleVal Val where coe := Val.ofSimpleVal

namespace EvalM

/-- take a single step in the machine. -/
def step (s : State) : EvalM State :=
  match s.error? with
  | .some error => s
  | .none => do -- not stuck, take a step.
     let v ← s.cur.evaluate


    match s.stack with
    | [] => .stackEmptyForValue
            
          

  


end EvalM
end Eval

end Gradual
def foo : IO Unit := return ()
