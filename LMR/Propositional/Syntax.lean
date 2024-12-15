import LMR.Util.Misc

/-- 論理式 -/
inductive PropForm where
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
  -- `Lean.quote` 等を使ってただの String に変換している
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


/- ## リテラル -/

/-- リテラル -/
inductive Lit where
  | tr  : Lit
  | fls : Lit
  | pos : String → Lit
  | neg : String → Lit
  deriving Repr, DecidableEq, Inhabited

namespace Lit

declare_syntax_cat varlit

syntax ident : varlit
syntax "-" ident : varlit

declare_syntax_cat proplit

syntax "lit!{" proplit "}" : term
syntax "⊤" : proplit
syntax "⊥" : proplit
syntax varlit : proplit

macro_rules
  | `(lit!{ ⊤ })           => `(tr)
  | `(lit!{ ⊥ })           => `(fls)
  | `(lit!{ - $x:ident })  => `(neg $(Lean.quote x.getId.toString))
  | `(lit!{ $x:ident })    => `(pos $(Lean.quote x.getId.toString))

end Lit

/--
### 否定標準形 (NNF)

否定標準形は、否定が内側に入る形の論理式。
たとえば `P := ¬ (A ∧ B)` は NNF ではない。
`¬ A ∨ ¬ B` は、`P` の NNF である。
-/
inductive NnfForm where
  | lit  (l : Lit)       : NnfForm
  | conj (p q : NnfForm) : NnfForm
  | disj (p q : NnfForm) : NnfForm
  deriving Repr, DecidableEq, Inhabited

namespace NnfForm

declare_syntax_cat nnfform

syntax "nnf!{" nnfform "}"  : term

syntax:max ident                        : nnfform
syntax "⊤"                              : nnfform
syntax "⊥"                              : nnfform
syntax:35 nnfform:36 " ∧ " nnfform:35   : nnfform
syntax:30 nnfform:31 " ∨ " nnfform:30   : nnfform
syntax:max "(" nnfform ")"              : nnfform
syntax:max "¬ " ident                   : nnfform

macro_rules
  | `(nnf!{$p:ident})   => `(NnfForm.lit (Lit.pos $(Lean.quote p.getId.toString)))
  | `(nnf!{¬ $p:ident}) => `(NnfForm.lit (Lit.neg $(Lean.quote p.getId.toString)))
  | `(nnf!{⊤})          => `(NnfForm.tr)
  | `(nnf!{⊥})          => `(NnfForm.fls)
  | `(nnf!{$p ∧ $q})    => `(NnfForm.conj nnf!{$p} nnf!{$q})
  | `(nnf!{$p ∨ $q})    => `(NnfForm.disj nnf!{$p} nnf!{$q})
  | `(nnf!{($p:nnfform)}) => `(nnf!{$p})

private def toString : NnfForm → String
  | lit (Lit.pos s)  => s
  | lit (Lit.neg s)  => "(¬ " ++ s ++ ")"
  | lit Lit.tr       => "⊤"
  | lit Lit.fls      => "⊥"
  | conj p q         => "(" ++ toString p ++ " ∧ " ++ toString q ++ ")"
  | disj p q         => "(" ++ toString p ++ " ∨ " ++ toString q ++ ")"

instance : ToString NnfForm := ⟨toString⟩

instance : Repr NnfForm where
  reprPrec f _ := s!"nnf!\{{toString f}}"

end NnfForm

/- ## 真理値割当 -/

/-- partial な真理値割り当て -/
def PropAssignment := List (String × Bool)

instance : Inhabited PropAssignment :=
  inferInstanceAs (Inhabited (List _))

/-- 真理値割り当てをリストから定義する -/
def PropAssignment.mk (vars : List (String × Bool)) : PropAssignment :=
  vars

syntax "propassign!{" varlit,* "}" : term
macro_rules
  | `( propassign!{ $[$vars:varlit],* }) => do
    let vals ← vars.mapM fun
      | `(varlit| $x:ident) => `(($(Lean.quote x.getId.toString), true))
      | `(varlit| -$x:ident) => `(($(Lean.quote x.getId.toString), false))
      | s => panic! s!"unexpected syntax '{s}'"
    `(PropAssignment.mk [$[$vals],*])

instance : Repr PropAssignment where
  reprPrec τ _ :=
    let vars := ", ".intercalate (τ.map fun (x, v) => if v then x else "-" ++ x)
    s!"propassign!\{{vars}}"

instance : ToString PropAssignment where
  toString τ :=
    let mapping := ", ".intercalate <|
      List.map (fun (x, v) => x ++ " ↦ " ++ if v then "⊤" else "⊥") τ
    s!"\{{mapping}}"

/-- 変数 `x : String` に対して、真理値割当 `τ : PropAssignment` における真理値を返す。未割り当ての場合は `none` を返す。 -/
def PropAssignment.eval? (τ : PropAssignment) (x : String) : Option Bool := Id.run do
  let τ : List _ := τ
  for (y, v) in τ do
    if y == x then return some v
  return none

/-- 変数 `x : String` に対して、真理値割当 `τ : PropAssignment` における真理値を返す。
未割当の場合は `false` を返す。-/
def PropAssignment.eval (τ : PropAssignment) (x : String) : Bool :=
  τ.eval? x |>.getD false
