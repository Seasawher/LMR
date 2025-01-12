import LMR.Propositional.Syntax

open PropForm

/-- 論理式に対して、真理値割当 `v` による評価を返す。-/
def PropForm.eval (v : PropAssignment) : PropForm → Bool
  | var s => v.eval s
  | tr => true
  | fls => false
  | neg A => !(eval v A)
  | conj A B => (eval v A) && (eval v B)
  | disj A B => (eval v A) || (eval v B)
  | impl A B => !(eval v A) || (eval v B)
  | biImpl A B => (!(eval v A) || (eval v B)) && (!(eval v B) || (eval v A))

private def propExample := prop!{p ∧ q ∧ s}

-- `s` に対する割当は未定義なので、`false` が割り当てられる。その結果 `false` と評価される。
#guard
  let v := PropAssignment.mk [("p", true), ("q", true), ("r", true)]
  ! propExample.eval v

-- ちゃんと全部 `true` にすれば `true` と評価される。
#guard
  let v := PropAssignment.mk [("p", true), ("q", true), ("s", true)]
  propExample.eval v

-- `propassign!` という構文で割当を作れる。
#check propassign!{p, q, -r}

#guard propExample.eval propassign!{p, q, s}

/-- 与えられたリストのすべてのサブリストのリストを、全体を先頭にして返す。-/
def allSublists {α : Type} : List α → List (List α)
  | [] => [[]]
  | (a :: as) =>
      let recval := allSublists as
      recval.map (a :: .) ++ recval

#eval allSublists ["p", "q"]

/-- 与えられた論理式の真理値表を返す。

Note: 真理値割当は未定義の変数に対して `false` を返すので、サブリストの全体を真理値割当の全体と同一視できる。
-/
def truthTable (A : PropForm) : List (List Bool × Bool) :=
  let vars := A.vars
  let assignments := (allSublists vars).map (fun l => PropAssignment.mk (l.map (., true)))
  let evalLine := fun v : PropAssignment => (vars.map v.eval, A.eval v)
  assignments.map evalLine

#eval truthTable prop!{p ∧ q ∧ s}

/-- 論理式が恒真(valid)かどうか判定する -/
def PropForm.isValid (A : PropForm) : Bool := List.all (truthTable A) Prod.snd

/-- 論理式が充足可能(satisfiable)かどうか判定する -/
def PropForm.isSat (A : PropForm) : Bool := List.any (truthTable A) Prod.snd

#guard ! propExample.isValid
#guard prop!{p → (q → p)}.isValid

#guard prop!{p → (q → p)}.isSat
#guard prop!{p → q}.isSat
#guard ! prop!{p ∧ ¬ p}.isSat

-- /-- リテラルの否定 -/
-- def Lit.negate : Lit → Lit
--   | tr   => fls
--   | fls  => tr
--   | pos s => neg s
--   | neg s => pos s

/-- 否定標準形の否定（の否定標準形）を求める -/
def NnfForm.neg : NnfForm → NnfForm
  | lit l    => lit l.negate
  | conj p q => disj (neg p) (neg q)
  | disj p q => conj (neg p) (neg q)

namespace PropForm



open NnfForm in

/-- 論理式を否定標準形に変形する -/
def toNnfForm : PropForm → NnfForm
  | tr         => lit Lit.tr
  | fls        => lit Lit.fls
  | var n      => lit (Lit.pos n)
  | neg p      => p.toNnfForm.neg
  | conj p q   => .conj p.toNnfForm q.toNnfForm
  | disj p q   => .disj p.toNnfForm q.toNnfForm
  | impl p q   => .disj p.toNnfForm.neg q.toNnfForm
  | biImpl p q =>
    .conj (.disj p.toNnfForm.neg q.toNnfForm)
      (.disj q.toNnfForm.neg p.toNnfForm)

#eval ToString.toString <| prop!{¬ (p ∧ ¬ (q ∨ r))}.toNnfForm

-- /-- クローズ（句） -/
-- def Clause := List Lit

-- /-- conjunction normal form(連言標準形) -/
-- def CnfForm := List Clause

private def exLit0 := lit!{ p }
private def exLit1 := lit!{ -q }

#print exLit0
#print exLit1

private def exClause0 := clause!{ p }
private def exClause1 := clause!{ p -q r }
private def exClause2 := clause!{ r -s }

#eval exClause0
#eval ToString.toString exClause1
#print exClause2

private def exCnf0 := cnf!{
  p,
  -p q -r,
  -p q
}

private def exCnf1 := cnf!{
  p -q,
  p q,
  -p -r,
  -p r
}

private def exCnf2 := cnf!{
  p q,
  -p,
  -q
}

#print exCnf0
#print exCnf1
#print exCnf2

#eval exCnf2
#eval toString exCnf2

end PropForm


#eval List.insert lit!{ r } exClause0

#eval exClause0.union' exClause1

#eval List.Union [exClause0, exClause1, exClause2]

#eval exCnf1.map exClause0.union'

def CnfForm.disj (cnf1 cnf2 : CnfForm) : CnfForm :=
  -- 分配法則使ってる（map して union してるのがそれ）
  (cnf1.map (fun cls => cnf2.map cls.union')).Union

#eval toString <| cnf!{ q, p }
#eval toString <| CnfForm.disj cnf!{ p } cnf!{ q, p }
-- `p ∨ (q ∧ p) = (p ∨ q) ∧ (p ∨ p)`
--           `_ = (p ∨ q) ∧ p`

#eval cnf!{p, q, u -v}.disj cnf!{r1 r2, s1 s2, t1 t2 t3}
#eval toString <| cnf!{p, q, u -v}.disj cnf!{r1 r2, s1 s2, t1 t2 t3}

