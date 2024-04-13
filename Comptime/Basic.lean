import Comptime.Env

namespace Comptime

section type
  inductive Ty where
    | num : Ty
    | pair (t₁ t₂ : Ty) : Ty
    | arrow (dom rng : Ty) : Ty
    | comp (t : Ty) : Ty
    | dummy : Ty

  notation:10 x " t→ " y =>
    Ty.arrow x y
end type

section expr
  inductive Expr where
    | num (n : ℕ) : Expr
    | add (e₁ e₂ : Expr) : Expr
    | pair (e₁ e₂ : Expr) : Expr
    | fst (e : Expr) : Expr
    | snd (e : Expr) : Expr
    | lam (name : String) (Ty : Ty) (body : Expr) : Expr
    | app (func arg : Expr) : Expr
    | var (name : String) : Expr
    | comp (e : Expr) : Expr

  instance : OfNat Expr n where
    ofNat := .num n

  @[simp]
  def Expr.let (x : String) (t : Ty) (v body : Expr) : Expr :=
    Expr.app (Expr.lam x t body) v
end expr

section rexpr
  inductive RExpr where
    | num (n : ℕ) : RExpr
    | add (r₁ r₂ : RExpr) : RExpr
    | pair (r₁ r₂ : RExpr) : RExpr
    | fst (r : RExpr) : RExpr
    | snd (r : RExpr) : RExpr
    | lam (name : String) (t : Ty) (body : RExpr) : RExpr
    | app (func arg : RExpr) : RExpr
    | var (name : String) : RExpr
    | comp_closure (keys : Finset String)
                   (env : keys -> RExpr)
                   (name : String)
                   (t : Ty)
                   (e : Expr) : RExpr

  instance : OfNat RExpr n where
    ofNat := .num n

  @[simp]
  def RExpr.let (x : String) (t : Ty) (v body : RExpr) : RExpr :=
    RExpr.app (RExpr.lam x t body) v
end rexpr

section value
  inductive Value where
    | num (n : ℕ) : Value
    | pair (v₁ v₂ : Value) : Value
    | closure (keys : Finset Name)
              (renv : keys → Value)
              (name : Name)
              (t : Ty)
              (body : RExpr) : Value

  instance : OfNat Value n where
    ofNat := .num n
end value

end Comptime
