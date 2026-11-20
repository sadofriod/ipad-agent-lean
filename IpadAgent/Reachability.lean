import IpadAgent.Transition

/-!
### 3. 可达状态

`Reachable` 表示从初始状态出发、重复应用 `Step` 可以得到的状态。
它的两个构造子分别给出归纳证明的基例和归纳步。
-/
namespace IpadAgent

inductive Reachable (hash : String → Digest) : St → Prop where
  | init : Reachable hash (initSt hash)
  | step {s s' : St} {a : Act} : Reachable hash s → Step hash s a s' → Reachable hash s'

end IpadAgent
