import Mathlib.Tactic.Linarith.Frontend

inductive Typ where
  | num : Typ
  | pair (t₁ t₂ : Typ) : Typ
  | func (t₁ t₂ : Typ) : Typ
  | comp (t : Typ) : Typ

inductive RExpr where
  | num (n : ℕ) : RExpr
  | add (r₁ r₂ : RExpr) : RExpr
  | pair (r₁ r₂ : RExpr) : RExpr
  | fst (r : RExpr) : RExpr
  | snd (r : RExpr) : RExpr
  | func (name : ℕ) (typ : Typ) (body : RExpr) : RExpr
  | app (rfunc rarg : RExpr) : RExpr
  | var (name : ℕ) : RExpr

inductive Expr where
  | num (n : ℕ) : Expr
  | add (e₁ e₂ : ℕ) : Expr
  | pair (e₁ e₂ : Expr) : Expr
  | fst (e : Expr) : Expr
  | snd (e : Expr) : Expr
  | func (name : ℕ) (typ : Typ) (body : Expr) : Expr
  | app (efunc earg : Expr) : Expr
  | var (name : ℕ) : Expr
  | comp (e : Expr) : Expr

inductive Value where
  | num (n : ℕ) : Value
  | pair (v₁ v₂ : Value) : Value
  | closure (renv : List Value) (name : ℕ) (typ : Typ) (body : RExpr) : Value

def REnv := List Value

inductive Eval : RExpr → REnv → Value → Prop where
  | num : Eval (RExpr.num n) _ (Value.num n)
  | add (h₁ : Eval r₁ renv (Value.num n₁)) (h₂ : Eval r₂ renv (Value.num n₂))
        (hadd : n₃ = n₁ + n₂) :
        Eval (RExpr.add r₁ r₂) renv (Value.num n₃)
  | pair (h₁ : Eval r₁ renv v₁) (h₂ : Eval r₂ renv v₂) :
         Eval (RExpr.pair r₁ r₂) renv (Value.pair v₁ v₂)
  | fst (h : Eval r renv (Value.pair v₁ v₂)) : Eval (RExpr.fst r) renv v₁
  | snd (h : Eval r renv (Value.pair v₁ v₂)) : Eval (RExpr.snd r) renv v₂
  | var (h : i < renv.length) : Eval (RExpr.var i) renv (renv.get ⟨i, h⟩)
  | func : Eval (RExpr.func name typ body) renv (Value.closure renv name typ body)
  | app (hfunc : Eval rfunc renv (Value.closure renv' name typ body))
        (harg : Eval rarg renv varg)
        (hbody : Eval body (renv'.set name varg) vres) :
        Eval (RExpr.app rfunc rarg) renv vres

example (n : ℕ) : Eval (RExpr.num (n+1)) [] (Value.num (n+1)) := by {
  constructor
}

example : Eval (RExpr.var 1) [Value.num 1, Value.num 2] (Value.num 2) := by {
  constructor
  simp
}

example : Eval (RExpr.app (RExpr.func 1 Typ.num (RExpr.add (RExpr.var 1) (RExpr.num 1)))
                          (RExpr.num 42))
               [Value.num 0, Value.num 0]
               (Value.num 43) := by {
  constructor <;> constructor <;> constructor ; simp
}
