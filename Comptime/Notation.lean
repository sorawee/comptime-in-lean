import Comptime.Basic
import Lean

open Lean Elab Term

def getImpl (proc : Name → Syntax → Expr → TermElabM (TSyntax `term)) : TermElab :=
  fun stx typ? => do
    tryPostponeIfNoneOrMVar typ?
    let some typ := typ? | throwError "expected type must be known "
    if typ.isMVar then
      throwError "expected type must be known"
    let Expr.const base .. := typ | throwError s!"type is not of the expected form: {typ}"
    let stx ← proc base stx typ
    elabTerm stx typ

section app_notation
  syntax (name := app_notation) term " @ " term : term

  @[term_elab app_notation]
  def applicationImpl : TermElab := getImpl (fun base stx typ =>
    if base = .str (.str .anonymous "Comptime") "Expr" then
      `(Comptime.Expr.app $(TSyntax.mk stx[0]) $(TSyntax.mk stx[2]))
    else if base = .str (.str .anonymous "Comptime") "RExpr" then
      `(Comptime.RExpr.app $(TSyntax.mk stx[0]) $(TSyntax.mk stx[2]))
    else
      throwError s!"unsupported type: {typ}")
end app_notation

section lambda_notation
  syntax (name := lambda_notation) "Λ" "(" term " : " term ")" " => " term : term

  @[term_elab lambda_notation]
  def lambdaImpl : TermElab := getImpl (fun base stx typ =>
    if base = .str (.str .anonymous "Comptime") "Expr" then
      `(Comptime.Expr.lam $(TSyntax.mk stx[2]) $(TSyntax.mk stx[4]) $(TSyntax.mk stx[7]))
    else if base = .str (.str .anonymous "Comptime") "RExpr" then
      `(Comptime.RExpr.lam $(TSyntax.mk stx[2]) $(TSyntax.mk stx[4]) $(TSyntax.mk stx[7]))
    else
      throwError s!"unsupported type: {typ}")
end lambda_notation

section comp_notation
  syntax (name := comp_notation) "$⟨" term "⟩" : term

  @[term_elab comp_notation]
  def compImpl : TermElab := getImpl (fun base stx typ =>
    if base = .str (.str .anonymous "Comptime") "Expr" then
      `(Comptime.Expr.comp $(TSyntax.mk stx[1]))
    else if base = .str (.str .anonymous "Comptime") "Ty" then
      `(Comptime.Ty.comp $(TSyntax.mk stx[1]))
    else
      throwError s!"unsupported type: {typ}")
end comp_notation

section let_notation
  syntax (name := let_notation) "let_" term " :~ " term " := " term " in " term : term

  @[term_elab let_notation]
  def letImpl : TermElab := getImpl (fun base stx typ =>
    if base = .str (.str .anonymous "Comptime") "Expr" then
      `(Comptime.Expr.let
        $(TSyntax.mk stx[1]) $(TSyntax.mk stx[3]) $(TSyntax.mk stx[5]) $(TSyntax.mk stx[7]))
    else if base = .str (.str .anonymous "Comptime") "RExpr" then
      `(Comptime.RExpr.let
        $(TSyntax.mk stx[1]) $(TSyntax.mk stx[3]) $(TSyntax.mk stx[5]) $(TSyntax.mk stx[7]))
    else
      throwError s!"unsupported type: {typ}")
end let_notation

/-
Another possibility is to use the Add class, which will allow us to use
the normal + on Expr and RExpr. Unfortunately, Add doesn't propagate types as well,
so we opt to follow this route instead.
-/
section add_notation
  syntax (name := add_notation) term " +_ " term : term

  @[term_elab add_notation]
  def addImpl : TermElab := getImpl (fun base stx typ =>
    if base = .str (.str .anonymous "Comptime") "Expr" then
      `(Comptime.Expr.add $(TSyntax.mk stx[0]) $(TSyntax.mk stx[2]))
    else if base = .str (.str .anonymous "Comptime") "RExpr" then
      `(Comptime.RExpr.add $(TSyntax.mk stx[0]) $(TSyntax.mk stx[2]))
    else
      throwError s!"unsupported type: {typ}")
end add_notation
