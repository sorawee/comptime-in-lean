import Mathlib
import Comptime.Env
import Comptime.Basic
import Comptime.Notation

namespace Comptime

inductive Eval : RExpr → Env Value → Value → Prop where
  | num : Eval (.num n) _ (.num n)
  | add (h₁ : Eval r₁ renv (.num n₁)) (h₂ : Eval r₂ renv (.num n₂))
        (hadd : n₃ = n₁ + n₂) :
        Eval (r₁ + r₂) renv (.num n₃)
  | pair (h₁ : Eval r₁ renv v₁) (h₂ : Eval r₂ renv v₂) :
         Eval (.pair r₁ r₂) renv (.pair v₁ v₂)
  | fst (h : Eval r renv (.pair v₁ v₂)) : Eval (.fst r) renv v₁
  | snd (h : Eval r renv (.pair v₁ v₂)) : Eval (.snd r) renv v₂
  | var (h : x ∈ renv.keys) (hlook : v = renv.env ⟨x, h⟩) : Eval (.var x) renv v
  | lam : Eval (Λ (name : t) => body) renv (.closure renv.keys renv.env name t body)
  | app (hfunc : Eval rfunc renv (.closure keys' renv' name t body))
        (harg : Eval rarg renv varg)
        (hbody : Eval body ({keys := keys', env := renv'}{name ↦ varg}) vres) :
        Eval (rfunc @ rarg) renv vres

inductive Comp : Expr → Env RExpr → RExpr → Prop where
  | num : Comp (.num n) _ (.num n)
  | num' : Comp $⟨.num n⟩ _ (.num n)
  | add (h₁ : Comp e₁ cenv r₁) (h₂ : Comp e₂ cenv r₂) :
        Comp (e₁ + e₂) cenv (r₁ + r₂)
  | add' (h₁ : Comp e₁ cenv r₁) (h₂ : Comp e₂ cenv r₂) :
         Comp $⟨e₁ + e₂⟩ cenv (r₁ + r₂)
  | pair (h₁ : Comp e₁ cenv r₁) (h₂ : Comp e₂ cenv r₂) :
         Comp (.pair e₁ e₂) cenv (.pair r₁ r₂)
  | pair' (h₁ : Comp e₁ cenv r₁) (h₂ : Comp e₂ cenv r₂) :
          Comp $⟨.pair e₁ e₂⟩ cenv (.pair r₁ r₂)
  | fst (h : Comp e cenv r) : Comp (.fst e) cenv (.fst r)
  | snd (h : Comp e cenv r) : Comp (.snd e) cenv (.snd r)
  | fst' (h : Comp e cenv r) : Comp $⟨.fst e⟩ cenv (.fst r)
  | snd' (h : Comp e cenv r) : Comp $⟨.snd e⟩ cenv (.snd r)
  | var (h : x ∈ cenv.keys) : Comp (.var i) cenv (cenv.env ⟨x, h⟩)
  | var' (h : x ∈ cenv.keys) : Comp $⟨.var i⟩ cenv (cenv.env ⟨x, h⟩)
  | lam (hbody : Comp body (cenv{x ↦ .var x}) body') :
        Comp (Λ (x : t) => body) cenv (Λ (x : t) => body')
  | lam' : Comp $⟨Λ (x : t) => body⟩ cenv (.comp_closure cenv.keys cenv.env x t body)
  | app (hfunc : Comp efunc cenv rfunc)
        (harg : Comp earg cenv rarg) :
        Comp (efunc @ earg) cenv (rfunc @ rarg)
  | app' (hfunc : Comp efunc cenv (.comp_closure keys' env' name t body))
         (harg : Comp earg cenv rarg)
         (hbody : Comp body ({keys := keys', env := env'}{name ↦ rarg}) rres) :
         Comp $⟨efunc @ earg⟩ cenv rres
  | flatten (h : Comp $⟨e⟩ cenv r) : Comp $⟨$⟨e⟩⟩ cenv r

inductive TyCheck : Expr → Env Ty → Env Ty → Ty → Prop where
  | num : TyCheck (.num _) _ _ .num
  | num' : TyCheck $⟨.num _⟩ _ _ $⟨.num⟩
  | add (h₁ : TyCheck e₁ renv cenv .num)
        (h₂ : TyCheck e₂ renv cenv .num) :
        TyCheck (e₁ + e₂) renv cenv .num
  | add' (h₁ : TyCheck $⟨e₁⟩ renv cenv $⟨.num⟩)
         (h₂ : TyCheck $⟨e₂⟩ renv cenv $⟨.num⟩) :
         TyCheck $⟨e₁ + e₂⟩ renv cenv $⟨.num⟩
  | pair (h₁ : TyCheck e₁ renv cenv t₁)
         (h₂ : TyCheck e₂ renv cenv t₂) :
         TyCheck (.pair e₁ e₂) renv cenv (.pair t₁ t₂)
  | pair' (h₁ : TyCheck $⟨e₁⟩ renv cenv $⟨t₁⟩)
          (h₂ : TyCheck $⟨e₂⟩ renv cenv $⟨t₂⟩) :
          TyCheck $⟨.pair e₁ e₂⟩ renv cenv $⟨.pair t₁ t₂⟩
  | fst (h : TyCheck e renv cenv (.pair t₁ t₂)) :
        TyCheck (.fst e) renv cenv t₁
  | fst' (h : TyCheck $⟨e⟩ renv cenv $⟨.pair t₁ t₂⟩) :
         TyCheck $⟨.fst e⟩ renv cenv $⟨t₁⟩
  | snd (h : TyCheck e renv cenv (.pair t₁ t₂)) :
        TyCheck (.snd e) renv cenv t₂
  | snd' (h : TyCheck $⟨e⟩ renv cenv $⟨.pair t₁ t₂⟩) :
         TyCheck $⟨.snd e⟩ renv cenv $⟨t₂⟩
  | var (h : x ∈ renv.keys) : TyCheck (.var x) renv cenv (renv.env ⟨x, h⟩)
  | var' (h : x ∈ cenv.keys) : TyCheck $⟨.var x⟩ renv cenv (cenv.env ⟨x, h⟩)
  | lam (h : TyCheck e (renv{x ↦ t}) cenv t') :
        TyCheck (Λ (x : t) => e) renv cenv (t t→ t')
  | lam' (h : TyCheck e ∅ (cenv{x ↦ t}) t') :
         TyCheck $⟨Λ (x : t) => e⟩ _ cenv $⟨t t→ t'⟩
  | app (hfun : TyCheck ef renv cenv (t t→ t'))
        (harg : TyCheck ea renv cenv t) :
        TyCheck (ef @ ea) renv cenv t'

def ex : Expr :=
  let_ "exp" :~ .dummy := $⟨Λ ("n" : .num) => (.var "n")⟩ in
    let_ "x" :~ .dummy := $⟨3⟩ in
      ((.var "exp") @ 5) @ $⟨((.var "exp") @ 2) @ (.var "x")⟩

example (n : ℕ) : Eval (.num (n+1)) ∅ (.num (n+1)) := by {
  constructor
}

example : Eval (.var "x") (∅{"x" ↦ 2}) 2 := by {
  constructor <;> simp
}

example : Eval ((Λ ("x" : (.num t→ .num)) => (RExpr.var "x") + 1) @ 42) ∅ 43 := by {
  constructor <;> constructor <;> constructor <;> simp
}

end Comptime
