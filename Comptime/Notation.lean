import Comptime.Basic
import Lean

open Lean Elab Term

section app_notation
  syntax (name := app_notation) term "@" term : term

  @[term_elab app_notation]
  def applicationImpl : TermElab := fun stx typ? => do
    tryPostponeIfNoneOrMVar typ?
    let some typ := typ? |
      let x := elabTerm stx[0] .none
      throwError "expected type must be known "
    if typ.isMVar then
      throwError "expected type must be known"
    let Expr.const base .. := typ | throwError s!"type is not of the expected form: {typ}"
    let stx ← if base = .str (.str .anonymous "Comptime") "Expr" then
      `(Comptime.Expr.app $(TSyntax.mk stx[0]) $(TSyntax.mk stx[2]))
    else if base = .str (.str .anonymous "Comptime") "RExpr" then
      `(Comptime.RExpr.app $(TSyntax.mk stx[0]) $(TSyntax.mk stx[2]))
    else
      throwError s!"unsupported type: {typ}"
    elabTerm stx typ
end app_notation

section lambda_notation
  syntax (name := lambda_notation) "Λ" "(" term " : " term ")" " => " term : term

  @[term_elab lambda_notation]
  def lambdaImpl : TermElab := fun stx typ? => do
    tryPostponeIfNoneOrMVar typ?
    let some typ := typ? | throwError "expected type must be known"
    if typ.isMVar then
      throwError "expected type must be known"
    let Expr.const base .. := typ | throwError s!"type is not of the expected form: {typ}"
    let stx ← if base = .str (.str .anonymous "Comptime") "Expr" then
      `(Comptime.Expr.lam $(TSyntax.mk stx[2]) $(TSyntax.mk stx[4]) $(TSyntax.mk stx[7]))
    else if base = .str (.str .anonymous "Comptime") "RExpr" then
      `(Comptime.RExpr.lam $(TSyntax.mk stx[2]) $(TSyntax.mk stx[4]) $(TSyntax.mk stx[7]))
    else
      throwError s!"unsupported type: {typ}"
    elabTerm stx typ
end lambda_notation

section comp_notation
  syntax (name := comp_notation) "$⟨" term "⟩" : term

  @[term_elab comp_notation]
  def compImpl : TermElab := fun stx typ? => do
    tryPostponeIfNoneOrMVar typ?
    let some typ := typ? | throwError "expected type must be known"
    if typ.isMVar then
      throwError "expected type must be known"
    let Expr.const base .. := typ | throwError s!"type is not of the expected form: {typ}"
    let stx ← if base = .str (.str .anonymous "Comptime") "Expr" then
      `(Comptime.Expr.comp $(TSyntax.mk stx[1]))
    else if base = .str (.str .anonymous "Comptime") "Ty" then
      `(Comptime.Ty.comp $(TSyntax.mk stx[1]))
    else
      throwError s!"unsupported type: {typ}"
    elabTerm stx typ
end comp_notation

section let_notation
  syntax (name := let_notation) "let_" term " :~ " term " := " term " in " term : term

  @[term_elab let_notation]
  def letImpl : TermElab := fun stx typ? => do
    tryPostponeIfNoneOrMVar typ?
    let some typ := typ? | throwError "expected type must be known"
    if typ.isMVar then
      throwError "expected type must be known"
    let Expr.const base .. := typ | throwError s!"type is not of the expected form: {typ}"
    let stx ← if base = .str (.str .anonymous "Comptime") "Expr" then
      `(Comptime.Expr.let
        $(TSyntax.mk stx[1]) $(TSyntax.mk stx[3]) $(TSyntax.mk stx[5]) $(TSyntax.mk stx[7]))
    else if base = .str (.str .anonymous "Comptime") "RExpr" then
      `(Comptime.RExpr.let
        $(TSyntax.mk stx[1]) $(TSyntax.mk stx[3]) $(TSyntax.mk stx[5]) $(TSyntax.mk stx[7]))
    else
      throwError s!"unsupported type: {typ}"
    elabTerm stx typ
end let_notation
