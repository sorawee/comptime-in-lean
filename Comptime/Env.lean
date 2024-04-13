import Mathlib.Data.Finset.Basic

structure Env (τ : Type u) where
  {keys : Finset String}
  env : keys -> τ

instance : EmptyCollection (Env τ) :=
  ⟨{ keys := Finset.empty, env := default }⟩

namespace Env

variable {τ : Type u}

@[simp]
def update (e : Env τ) (k : String) (v : τ) : Env τ :=
  { keys := insert k e.keys
    env := fun kn => by {
      by_cases kn = k
      case pos => exact v
      case neg h =>
        have prop := kn.property
        simp [h] at prop
        exact e.env ⟨kn.val, prop⟩
    }}

notation:10 d "{" k " ↦ " v "}" => Env.update d k v

end Env
