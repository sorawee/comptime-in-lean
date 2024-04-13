import Comptime.Env

section type
  inductive Ty where
    | num : Ty
    | pair (t₁ t₂ : Ty) : Ty
    | arrow (dom rng : Ty) : Ty
    | comp (t : Ty) : Ty
    | dummy : Ty

  notation:10 x " t→ " y =>
    Ty.arrow x y

  notation:10 "$t" "⟨" t "⟩" =>
    Ty.comp t
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

  notation:10 "eλ" "(" x " : " t ")" " => " body =>
    Expr.lam x t body

  notation:10 x " e+ " y =>
    Expr.add x y

  notation:10 x " e@ " y =>
    Expr.app x y

  notation:10 "$e" "⟨" e "⟩" =>
    Expr.comp e

  instance : OfNat Expr n where
    ofNat := .num n

  def Expr.let (x : String) (t : Ty) (v body : Expr) : Expr :=
    (eλ (x : t) => body) e@ v

  notation:10 "elet" x " :~ " t " := " v " in " body  =>
    Expr.let x t v body
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

  notation:10 "rλ" "(" x " : " t ")" " => " body =>
    RExpr.lam x t body

  notation:10 x " r+ " y =>
    RExpr.add x y

  notation:10 x " r@ " y =>
    RExpr.app x y

  instance : OfNat RExpr n where
    ofNat := .num n

  def RExpr.let (x : String) (t : Ty) (v body : RExpr) : RExpr :=
    (rλ (x : t) => body) r@ v

  notation:10 "rlet" x " :: " t " := " v " in " body  =>
    RExpr.let x t v body

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
