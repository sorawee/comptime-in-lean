import Mathlib

notation:10 xs "[" x "↦" v "]" =>
  List.set xs x v

inductive Typ where
  | num : Typ
  | pair (t₁ t₂ : Typ) : Typ
  | arrow (dom rng : Typ) : Typ
  | comp (t : Typ) : Typ

notation:10 x " t-> " y =>
  Typ.arrow x y

inductive Expr where
  | num (n : ℕ) : Expr
  | add (e₁ e₂ : Expr) : Expr
  | pair (e₁ e₂ : Expr) : Expr
  | fst (e : Expr) : Expr
  | snd (e : Expr) : Expr
  | lam (name : ℕ) (typ : Typ) (body : Expr) : Expr
  | app (func arg : Expr) : Expr
  | var (name : ℕ) : Expr
  | comp (e : Expr) : Expr

inductive RExpr where
  | num (n : ℕ) : RExpr
  | add (r₁ r₂ : RExpr) : RExpr
  | pair (r₁ r₂ : RExpr) : RExpr
  | fst (r : RExpr) : RExpr
  | snd (r : RExpr) : RExpr
  | lam (name : ℕ) (typ : Typ) (body : RExpr) : RExpr
  | app (func arg : RExpr) : RExpr
  | var (name : ℕ) : RExpr
  | comp_closure (cenv : List RExpr) (name : ℕ) (t : Typ) (e : Expr) : RExpr

notation:10 "rλ" "(" x " : " t ")" " => " body =>
  RExpr.lam x t body

notation:10 x " r+ " y =>
  RExpr.add x y

notation:10 x " r@ " y =>
  RExpr.app x y

instance : OfNat RExpr n where
  ofNat := RExpr.num n

notation:10 "eλ" "(" x " : " t ")" " => " body =>
  Expr.lam x t body

notation:10 x " e+ " y =>
  Expr.add x y

notation:10 x " e@ " y =>
  Expr.app x y

notation:10 "$t" "⟨" t "⟩" =>
  Typ.comp t

notation:10 "$e" "⟨" e "⟩" =>
  Expr.comp e

instance : OfNat Expr n where
  ofNat := Expr.num n

inductive Value where
  | num (n : ℕ) : Value
  | pair (v₁ v₂ : Value) : Value
  | closure (renv : List Value) (name : ℕ) (typ : Typ) (body : RExpr) : Value

instance : OfNat Value n where
  ofNat := Value.num n

def REnv := List Value
def CEnv := List RExpr
def TEnv := List Typ

inductive Eval : RExpr → REnv → Value → Prop where
  | num : Eval (RExpr.num n) _ (Value.num n)
  | add (h₁ : Eval r₁ renv (Value.num n₁)) (h₂ : Eval r₂ renv (Value.num n₂))
        (hadd : n₃ = n₁ + n₂) :
        Eval (r₁ r+ r₂) renv (Value.num n₃)
  | pair (h₁ : Eval r₁ renv v₁) (h₂ : Eval r₂ renv v₂) :
         Eval (RExpr.pair r₁ r₂) renv (Value.pair v₁ v₂)
  | fst (h : Eval r renv (Value.pair v₁ v₂)) : Eval (RExpr.fst r) renv v₁
  | snd (h : Eval r renv (Value.pair v₁ v₂)) : Eval (RExpr.snd r) renv v₂
  | var (h : i < renv.length) : Eval (RExpr.var i) renv (renv.get ⟨i, h⟩)
  | lam : Eval (rλ (name : typ) => body) renv (Value.closure renv name typ body)
  | app (hfunc : Eval rfunc renv (Value.closure renv' name typ body))
        (harg : Eval rarg renv varg)
        (hbody : Eval body (renv'[name ↦ varg]) vres) :
        Eval (rfunc r@ rarg) renv vres

inductive Comp : Expr → CEnv → RExpr → Prop where
  | num : Comp (Expr.num n) _ (RExpr.num n)
  | num' : Comp ($e⟨Expr.num n⟩) _ (RExpr.num n)
  | add (h₁ : Comp e₁ cenv r₁) (h₂ : Comp e₂ cenv r₂) :
        Comp (e₁ e+ e₂) cenv (r₁ r+ r₂)
  | add' (h₁ : Comp e₁ cenv r₁) (h₂ : Comp e₂ cenv r₂) :
         Comp ($e⟨e₁ e+ e₂⟩) cenv (r₁ r+ r₂)
  | pair (h₁ : Comp e₁ cenv r₁) (h₂ : Comp e₂ cenv r₂) :
         Comp (Expr.pair e₁ e₂) cenv (RExpr.pair r₁ r₂)
  | pair' (h₁ : Comp e₁ cenv r₁) (h₂ : Comp e₂ cenv r₂) :
          Comp ($e⟨Expr.pair e₁ e₂⟩) cenv (RExpr.pair r₁ r₂)
  | fst (h : Comp e cenv r) : Comp (Expr.fst e) cenv (RExpr.fst r)
  | snd (h : Comp e cenv r) : Comp (Expr.snd e) cenv (RExpr.snd r)
  | fst' (h : Comp e cenv r) : Comp ($e⟨Expr.fst e⟩) cenv (RExpr.fst r)
  | snd' (h : Comp e cenv r) : Comp ($e⟨Expr.snd e⟩) cenv (RExpr.snd r)
  | var (h : i < cenv.length) : Comp (Expr.var i) cenv (cenv.get ⟨i, h⟩)
  | var' (h : i < cenv.length) : Comp ($e⟨Expr.var i⟩) cenv (cenv.get ⟨i, h⟩)
  | lam (hbody : Comp body (cenv[x ↦ (RExpr.var x)]) body') :
        Comp (eλ (x : t) => body) cenv (rλ (x : t) => body')
  | lam' : Comp ($e⟨eλ (x : t) => body⟩) cenv (RExpr.comp_closure cenv x t body)
  | app (hfunc : Comp efunc cenv rfunc)
        (harg : Comp earg cenv rarg) :
        Comp (efunc e@ earg) cenv (rfunc r@ rarg)
  | app' (hfunc : Comp efunc cenv (RExpr.comp_closure cenv' name typ body))
         (harg : Comp earg cenv rarg)
         (hbody : Comp body (cenv'[name ↦ rarg]) rres) :
         Comp ($e⟨efunc e@ earg⟩) cenv rres
  | flatten (h : Comp ($e⟨e⟩) cenv r) : Comp ($e⟨$e⟨e⟩⟩) cenv r

inductive TypCheck : Expr → TEnv → Typ → Prop where
  | num : TypCheck (Expr.num _) _ Typ.num
  | num' : TypCheck ($e⟨Expr.num _⟩) _ ($t⟨Typ.num⟩)
  | add (h₁ : TypCheck e₁ tenv Typ.num)
        (h₂ : TypCheck e₂ tenv Typ.num) :
        TypCheck (e₁ e+ e₂) tenv Typ.num
  | add' (h₁ : TypCheck ($e⟨e₁⟩) tenv ($t⟨Typ.num⟩))
         (h₂ : TypCheck ($e⟨e₂⟩) tenv ($t⟨Typ.num⟩)) :
         TypCheck ($e⟨e₁ e+ e₂⟩) tenv ($t⟨Typ.num⟩)
  | pair (h₁ : TypCheck e₁ tenv t₁)
         (h₂ : TypCheck e₂ tenv t₂) :
         TypCheck (Expr.pair e₁ e₂) tenv (Typ.pair t₁ t₂)
  | pair' (h₁ : TypCheck ($e⟨e₁⟩) tenv ($t⟨t₁⟩))
          (h₂ : TypCheck ($e⟨e₂⟩) tenv ($t⟨t₂⟩)) :
          TypCheck ($e⟨Expr.pair e₁ e₂⟩) tenv ($t⟨Typ.pair t₁ t₂⟩)
  | fst (h : TypCheck e tenv (Typ.pair t₁ t₂)) :
        TypCheck (Expr.fst e) tenv t₁
  | fst' (h : TypCheck ($e⟨e⟩) tenv ($t⟨Typ.pair t₁ t₂⟩)) :
         TypCheck ($e⟨Expr.fst e⟩) tenv ($t⟨t₁⟩)
  | snd (h : TypCheck e tenv (Typ.pair t₁ t₂)) :
        TypCheck (Expr.snd e) tenv t₂
  | snd' (h : TypCheck ($e⟨e⟩) tenv ($t⟨Typ.pair t₁ t₂⟩)) :
         TypCheck ($e⟨Expr.snd e⟩) tenv ($t⟨t₂⟩)
  | var (h : i < tenv.length) : TypCheck (Expr.var i) tenv (tenv.get ⟨i, h⟩)
  -- | var' (h : i < tenv.length) : TypCheck ($e⟨Expr.var i⟩) tenv (tenv.get ⟨i, h⟩)
  | var' (h : i < tenv.length)
         (hget : tr = tenv.get ⟨i, h⟩)
         (hwell : tr = ($t⟨tx⟩)) :
         TypCheck ($e⟨Expr.var i⟩) tenv tr
  | lam (h : TypCheck e (tenv[i ↦ t]) t') :
        TypCheck (eλ (i : t) => e) tenv (t t-> t')
  | lam' (h : TypCheck e (tenv[i ↦ t]) t') :
         TypCheck ($e⟨eλ (i : t) => e⟩) tenv ($t⟨t t-> t'⟩)

example : Comp (($e⟨eλ (0 : Typ.num) => Expr.var 0⟩) e@ 1) [RExpr.var 99] (rλ (0 : Typ.num) => RExpr.var 0) := by {
  sorry
}

example (n : ℕ) : Eval (RExpr.num (n+1)) [] (Value.num (n+1)) := by {
  constructor
}

example : Eval (RExpr.var 1) [1, 2] 2 := by {
  constructor
  simp
}

example : Eval ((rλ (1 : (Typ.num t-> Typ.num)) => (RExpr.var 1) r+ 1)
                r@ 42)
               [0, 0]
               43 := by {
  constructor <;> constructor <;> constructor ; simp
}
