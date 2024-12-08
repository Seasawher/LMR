import LMR.Util.Misc

/-- 論理式 -/
inductive PropForm
  /-- 真 `⊤` -/
  | tr     : PropForm
  /-- 偽 `⊥` -/
  | fls    : PropForm
  /-- 命題変数 -/
  | var    : String → PropForm
  /-- 論理積 `∧` -/
  | conj   : PropForm → PropForm → PropForm
  /-- 論理和 `∨` -/
  | disj   : PropForm → PropForm → PropForm
  /-- 含意 `→` -/
  | impl   : PropForm → PropForm → PropForm
  /-- 否定 `¬` -/
  | neg    : PropForm → PropForm
  /-- 同値 `↔` -/
  | biImpl : PropForm → PropForm → PropForm
  deriving Repr, DecidableEq, Inhabited

open PropForm

-- コンストラクタを使って手動で頑張って論理式を定義している例
#check (impl (conj (var "p") (var "q")) (var "r"))

namespace PropForm

declare_syntax_cat propform

/-- `PropForm` を見やすく定義するための構文 -/
syntax "prop!{" propform "}"  : term

syntax:max ident                        : propform
syntax "⊤"                              : propform
syntax "⊥"                              : propform
syntax:35 propform:36 " ∧ " propform:35 : propform
syntax:30 propform:31 " ∨ " propform:30 : propform
syntax:20 propform:21 " → " propform:20 : propform
syntax:20 propform:21 " ↔ " propform:20 : propform
syntax:max "¬ " propform:40             : propform
syntax:max "(" propform ")"             : propform

macro_rules
  | `(prop!{$p:ident}) => `(PropForm.var $(Lean.quote p.getId.toString))
  | `(prop!{⊤})        => `(ProfForm.tr)
  | `(prop!{⊥})        => `(ProfForm.fls)
  | `(prop!{¬ $p})     => `(PropForm.neg prop!{$p})
  | `(prop!{$p ∧ $q})  => `(PropForm.conj prop!{$p} prop!{$q})
  | `(prop!{$p ∨ $q})  => `(PropForm.disj prop!{$p} prop!{$q})
  | `(prop!{$p → $q})  => `(PropForm.impl prop!{$p} prop!{$q})
  | `(prop!{$p ↔ $q})  => `(PropForm.biImpl prop!{$p} prop!{$q})
  | `(prop!{($p:propform)}) => `(prop!{$p})

#check prop!{p ∧ q → (r ∨ ¬ p) → q}
#check prop!{p ∧ q ∧ r → p}

private def propExample := prop!{p ∧ q → r ∧ p ∨ ¬ s1 → s2 }

#print propExample

-- `#eval` の結果はかなり複雑になる
#eval propExample

private def toString : PropForm → String
  | var s    => s
  | tr       => "⊤"
  | fls      => "⊥"
  | neg p    => "(¬ " ++ toString p ++ ")"
  | conj p q => "(" ++ toString p ++ " ∧ " ++ toString q ++ ")"
  | disj p q => "(" ++ toString p ++ " ∨ " ++ toString q ++ ")"
  | impl p q => "(" ++ toString p ++ " → " ++ toString q ++ ")"
  | biImpl p q => "(" ++ toString p ++ " ↔ " ++ toString q ++ ")"

instance : ToString PropForm := ⟨PropForm.toString⟩

-- `toString` で見やすく表示できるね
#eval propExample
#eval toString propExample

private def propExample₂ := prop!{p → (p → q)}

#eval toString propExample₂

/-- 論理式の複雑さ -/
def complexity : PropForm → Nat
  | var _ => 0
  | tr => 0
  | fls => 0
  | neg A => complexity A + 1
  | conj A B => complexity A + complexity B + 1
  | disj A B => complexity A + complexity B + 1
  | impl A B => complexity A + complexity B + 1
  | biImpl A B => complexity A + complexity B + 1

/-- 論理式の深さ -/
def depth : PropForm → Nat
  | var _ => 0
  | tr => 0
  | fls => 0
  | neg A => depth A + 1
  | conj A B => Nat.max (depth A) (depth B) + 1
  | disj A B => Nat.max (depth A) (depth B) + 1
  | impl A B => Nat.max (depth A) (depth B) + 1
  | biImpl A B => Nat.max (depth A) (depth B) + 1

/-- 論理式に含まれる変数のリスト -/
def vars : PropForm → List String
  | var s => [s]
  | tr => []
  | fls => []
  | neg A => vars A
  | conj A B => (vars A).union' (vars B)
  | disj A B => (vars A).union' (vars B)
  | impl A B => (vars A).union' (vars B)
  | biImpl A B => (vars A).union' (vars B)

#eval complexity propExample
#eval depth propExample
#eval vars propExample



end PropForm
